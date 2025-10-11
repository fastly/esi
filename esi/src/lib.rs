#![doc = include_str!("../README.md")]

mod config;
mod document;
mod error;
mod expression;
mod functions;
mod parse;

use crate::document::{FetchState, Task};
use crate::expression::{evaluate_expression, try_evaluate_interpolated, EvalContext};
use fastly::http::request::PendingRequest;
use fastly::http::{header, Method, StatusCode, Url};
use fastly::{mime, Body, Request, Response};
use log::{debug, error, trace};
use std::collections::VecDeque;
use std::io::{BufRead, Write};

pub use crate::document::{Element, Fragment};
pub use crate::error::Result;
pub use crate::parse::{parse_tags, Event, Include, Tag, Tag::Try};

pub use crate::config::Configuration;
pub use crate::error::ExecutionError;

// re-export quick_xml Reader and Writer
pub use quick_xml::{Reader, Writer};

type FragmentRequestDispatcher = dyn Fn(Request) -> Result<PendingFragmentContent>;

type FragmentResponseProcessor = dyn Fn(&mut Request, Response) -> Result<Response>;

/// Representation of a fragment that is either being fetched, has already been fetched (or generated synthetically), or skipped.
pub enum PendingFragmentContent {
    PendingRequest(PendingRequest),
    CompletedRequest(Response),
    NoContent,
}

impl From<PendingRequest> for PendingFragmentContent {
    fn from(value: PendingRequest) -> Self {
        Self::PendingRequest(value)
    }
}

impl From<Response> for PendingFragmentContent {
    fn from(value: Response) -> Self {
        Self::CompletedRequest(value)
    }
}

impl PendingFragmentContent {
    fn wait_for_content(self) -> Result<Response> {
        Ok(match self {
            Self::PendingRequest(pending_request) => pending_request.wait()?,
            Self::CompletedRequest(response) => response,
            Self::NoContent => Response::from_status(StatusCode::NO_CONTENT),
        })
    }
}

/// A processor for handling ESI responses
///
/// The Processor maintains state and configuration for processing ESI directives
/// in HTML/XML content. It handles fragment inclusion, variable substitution,
/// and conditional processing according to the ESI specification.
///
/// # Fields
/// * `original_request_metadata` - Optional original client request data used for fragment requests
/// * `configuration` - Configuration settings controlling ESI processing behavior
///
/// # Example
/// ```
/// use esi::{Processor, Configuration};
/// use fastly::Request;
///
/// // Create a configuration (assuming Configuration implements Default)
/// let config = Configuration::default();
///
/// // Optionally, create a Request (assuming Request can be constructed or mocked)
/// let request = Some(Request::get("http://example.com/"));
///
/// // Initialize the Processor with optional request metadata
/// let processor = Processor::new(request, config);
/// ```
pub struct Processor {
    // The original client request metadata, if any.
    original_request_metadata: Option<Request>,
    // The configuration for the processor.
    configuration: Configuration,
}

impl Processor {
    pub const fn new(
        original_request_metadata: Option<Request>,
        configuration: Configuration,
    ) -> Self {
        Self {
            original_request_metadata,
            configuration,
        }
    }

    /// Process a response body as an ESI document. Consumes the response body.
    ///
    /// This method processes ESI directives in the response body while streaming the output to the client,
    /// minimizing memory usage for large responses. It handles ESI includes, conditionals, and variable
    /// substitution according to the ESI specification.
    ///
    /// # Arguments
    /// * `src_document` - Source HTTP response containing ESI markup to process
    /// * `client_response_metadata` - Optional response metadata (headers, status) to send to client
    /// * `dispatch_fragment_request` - Optional callback for customizing fragment request handling
    /// * `process_fragment_response` - Optional callback for processing fragment responses
    ///
    /// # Returns
    /// * `Result<()>` - Ok if processing completed successfully, Error if processing failed
    ///
    /// # Example
    /// ```
    /// use fastly::Response;
    /// use esi::{Processor, Configuration};
    ///
    /// // Create a processor
    /// let processor = Processor::new(None, Configuration::default());
    ///
    /// // Create a response with ESI markup
    /// let mut response = Response::new();
    /// response.set_body("<esi:include src='http://example.com/header.html'/>");
    ///
    /// // Define a simple fragment dispatcher
    /// fn default_fragment_dispatcher(req: fastly::Request) -> esi::Result<esi::PendingFragmentContent> {
    ///     Ok(esi::PendingFragmentContent::CompletedRequest(
    ///         fastly::Response::from_body("Fragment content")
    ///     ))
    /// }
    /// // Process the response
    /// processor.process_response(
    ///     &mut response,
    ///     None,
    ///     Some(&default_fragment_dispatcher),
    ///     None
    /// )?;
    /// # Ok::<(), esi::ExecutionError>(())
    /// ```
    ///
    /// # Errors
    /// Returns error if:
    /// * ESI processing fails
    /// * Stream writing fails
    /// * Fragment requests fail
    pub fn process_response(
        self,
        src_document: &mut Response,
        client_response_metadata: Option<Response>,
        dispatch_fragment_request: Option<&FragmentRequestDispatcher>,
        process_fragment_response: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        // Create a response to send the headers to the client
        let resp = client_response_metadata.unwrap_or_else(|| {
            Response::from_status(StatusCode::OK).with_content_type(mime::TEXT_HTML)
        });

        // Send the response headers to the client and open an output stream
        let output_writer = resp.stream_to_client();

        // Set up an XML writer to write directly to the client output stream.
        let mut xml_writer = Writer::new(output_writer);

        match self.process_document(
            reader_from_body(src_document.take_body()),
            &mut xml_writer,
            dispatch_fragment_request,
            process_fragment_response,
        ) {
            Ok(()) => {
                xml_writer.into_inner().finish()?;
                Ok(())
            }
            Err(err) => {
                error!("error processing ESI document: {}", err);
                Err(err)
            }
        }
    }

    /// Process an ESI document that has already been parsed into a queue of events.
    ///
    /// Takes a queue of already parsed ESI events and processes them, writing the output
    /// to the provided writer. This method is used internally after parsing but can also
    /// be called directly if you have pre-parsed events.
    ///
    /// # Arguments
    /// * `src_events` - Queue of parsed ESI events to process
    /// * `output_writer` - Writer to stream processed output to
    /// * `dispatch_fragment_request` - Optional handler for fragment requests
    /// * `process_fragment_response` - Optional processor for fragment responses
    ///
    /// # Returns
    /// * `Result<()>` - Ok if processing completed successfully
    ///
    /// # Example
    /// ```
    /// use std::io::Cursor;
    /// use std::collections::VecDeque;
    /// use esi::{Event, Reader, Writer, Processor, Configuration};
    /// use quick_xml::events::Event as XmlEvent;
    ///
    /// let events = VecDeque::from([Event::Content(XmlEvent::Empty(
    ///     quick_xml::events::BytesStart::new("div")
    /// ))]);
    ///
    /// let mut writer = Writer::new(Cursor::new(Vec::new()));
    ///
    /// let processor = Processor::new(None, esi::Configuration::default());
    ///
    /// processor.process_parsed_document(
    ///     events,
    ///     &mut writer,
    ///     None,
    ///     None
    /// )?;
    /// # Ok::<(), esi::ExecutionError>(())
    /// ```
    ///
    /// # Errors
    /// Returns error if:
    /// * Event processing fails
    /// * Writing to output fails
    /// * Fragment request/response processing fails
    ///
    pub fn process_parsed_document(
        self,
        src_events: VecDeque<Event>,
        output_writer: &mut Writer<impl Write>,
        dispatch_fragment_request: Option<&FragmentRequestDispatcher>,
        process_fragment_response: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        // Set up fragment request dispatcher. Use what's provided or use a default
        let dispatch_fragment_request =
            dispatch_fragment_request.unwrap_or(&default_fragment_dispatcher);

        // If there is a source request to mimic, copy its metadata, otherwise use a default request.
        let original_request_metadata = self.original_request_metadata.as_ref().map_or_else(
            || Request::new(Method::GET, "http://localhost"),
            Request::clone_without_body,
        );

        // `root_task` is the root task that will be used to fetch tags in recursive manner
        let root_task = &mut Task::new();

        // context for the interpreter
        let mut ctx = EvalContext::new();
        ctx.set_request(original_request_metadata.clone_without_body());

        for event in src_events {
            event_receiver(
                event,
                &mut root_task.queue,
                self.configuration.is_escaped_content,
                &original_request_metadata,
                dispatch_fragment_request,
                &mut ctx,
            )?;
        }

        Self::process_root_task(
            root_task,
            output_writer,
            dispatch_fragment_request,
            process_fragment_response,
        )
    }

    /// Process an ESI document from a [`esi::Reader`], handling includes and directives
    ///
    /// Processes ESI directives while streaming content to the output writer. Handles:
    /// - ESI includes with fragment fetching
    /// - Variable substitution
    /// - Conditional processing
    /// - Try/except blocks
    ///
    /// # Arguments
    /// * `src_document` - Reader containing source XML/HTML with ESI markup
    /// * `output_writer` - Writer to stream processed output to
    /// * `dispatch_fragment_request` - Optional handler for fragment requests
    /// * `process_fragment_response` - Optional processor for fragment responses
    ///
    /// # Returns
    /// * `Result<()>` - Ok if processing completed successfully
    ///
    /// # Example
    /// ```
    /// use esi::{Reader, Writer, Processor, Configuration};
    /// use std::io::Cursor;
    ///
    /// let xml = r#"<esi:include src="http://example.com/header.html"/>"#;
    /// let reader = Reader::from_str(xml);
    /// let mut writer = Writer::new(Cursor::new(Vec::new()));
    ///
    /// let processor = Processor::new(None, Configuration::default());
    ///
    ///  // Define a simple fragment dispatcher
    /// fn default_fragment_dispatcher(req: fastly::Request) -> esi::Result<esi::PendingFragmentContent> {
    ///     Ok(esi::PendingFragmentContent::CompletedRequest(
    ///         fastly::Response::from_body("Fragment content")
    ///     ))
    /// }
    /// processor.process_document(
    ///     reader,
    ///     &mut writer,
    ///     Some(&default_fragment_dispatcher),
    ///     None
    /// )?;
    /// # Ok::<(), esi::ExecutionError>(())
    /// ```
    ///
    /// # Errors
    /// Returns error if:
    /// * ESI markup parsing fails
    /// * Fragment requests fail
    /// * Output writing fails
    pub fn process_document(
        self,
        mut src_document: Reader<impl BufRead>,
        output_writer: &mut Writer<impl Write>,
        dispatch_fragment_request: Option<&FragmentRequestDispatcher>,
        process_fragment_response: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        // Set up fragment request dispatcher. Use what's provided or use a default
        let dispatch_fragment_request =
            dispatch_fragment_request.unwrap_or(&default_fragment_dispatcher);

        // If there is a source request to mimic, copy its metadata, otherwise use a default request.
        let original_request_metadata = self.original_request_metadata.as_ref().map_or_else(
            || Request::new(Method::GET, "http://localhost"),
            Request::clone_without_body,
        );

        // `root_task` is the root task that will be used to fetch tags in recursive manner
        let root_task = &mut Task::new();

        // context for the interpreter
        let mut ctx = EvalContext::new();
        ctx.set_request(original_request_metadata.clone_without_body());

        // Call the library to parse fn `parse_tags` which will call the callback function
        // on each tag / event it finds in the document.
        // The callback function `handle_events` will handle the event.
        parse_tags(
            &self.configuration.namespace,
            &mut src_document,
            &mut |event| {
                event_receiver(
                    event,
                    &mut root_task.queue,
                    self.configuration.is_escaped_content,
                    &original_request_metadata,
                    dispatch_fragment_request,
                    &mut ctx,
                )
            },
        )?;

        Self::process_root_task(
            root_task,
            output_writer,
            dispatch_fragment_request,
            process_fragment_response,
        )
    }

    fn process_root_task(
        root_task: &mut Task,
        output_writer: &mut Writer<impl Write>,
        dispatch_fragment_request: &FragmentRequestDispatcher,
        process_fragment_response: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        // set the root depth to 0
        let mut depth = 0;

        debug!("Elements to fetch: {:?}", root_task.queue);

        // Elements dependent on backend requests are queued up.
        // The responses will need to be fetched and processed.
        // Go over the list for any pending responses and write them to the client output stream.
        fetch_elements(
            &mut depth,
            root_task,
            output_writer,
            dispatch_fragment_request,
            process_fragment_response,
        )?;

        Ok(())
    }
}

fn default_fragment_dispatcher(req: Request) -> Result<PendingFragmentContent> {
    debug!("no dispatch method configured, defaulting to hostname");
    let backend = req
        .get_url()
        .host()
        .unwrap_or_else(|| panic!("no host in request: {}", req.get_url()))
        .to_string();
    let pending_req = req.send_async(backend)?;
    Ok(PendingFragmentContent::PendingRequest(pending_req))
}

// This function is responsible for fetching pending requests and writing their
// responses to the client output stream. It also handles any queued source
// content that needs to be written to the client output stream.
fn fetch_elements(
    depth: &mut usize,
    task: &mut Task,
    output_writer: &mut Writer<impl Write>,
    dispatch_fragment_request: &FragmentRequestDispatcher,
    process_fragment_response: Option<&FragmentResponseProcessor>,
) -> Result<FetchState> {
    while let Some(element) = task.queue.pop_front() {
        match element {
            Element::Raw(raw) => {
                process_raw(task, output_writer, &raw, *depth)?;
            }
            Element::Include(fragment) => {
                let result = process_include(
                    task,
                    fragment,
                    output_writer,
                    *depth,
                    dispatch_fragment_request,
                    process_fragment_response,
                )?;
                if let FetchState::Failed(_, _) = result {
                    return Ok(result);
                }
            }
            Element::Try {
                mut attempt_task,
                mut except_task,
            } => {
                *depth += 1;
                process_try(
                    task,
                    output_writer,
                    &mut attempt_task,
                    &mut except_task,
                    depth,
                    dispatch_fragment_request,
                    process_fragment_response,
                )?;
                *depth -= 1;
                if *depth == 0 {
                    debug!(
                        "Writing try result: {:?}",
                        String::from_utf8(task.output.get_mut().as_slice().to_vec())
                    );
                    output_handler(output_writer, task.output.get_mut().as_ref())?;
                    task.output.get_mut().clear();
                }
            }
        }
    }
    Ok(FetchState::Succeeded)
}

fn process_include(
    task: &mut Task,
    fragment: Fragment,
    output_writer: &mut Writer<impl Write>,
    depth: usize,
    dispatch_fragment_request: &FragmentRequestDispatcher,
    process_fragment_response: Option<&FragmentResponseProcessor>,
) -> Result<FetchState> {
    // take the fragment and deconstruct it
    let Fragment {
        mut request,
        alt,
        continue_on_error,
        pending_content,
    } = fragment;

    // wait for `<esi:include>` request to complete
    let resp = pending_content.wait_for_content()?;

    let processed_resp = if let Some(process_response) = process_fragment_response {
        process_response(&mut request, resp)?
    } else {
        resp
    };

    // Request has completed, check the status code.
    if processed_resp.get_status().is_success() {
        if depth == 0 && task.output.get_mut().is_empty() {
            debug!("Include is not nested, writing content to the output stream");
            output_handler(output_writer, &processed_resp.into_body_bytes())?;
        } else {
            debug!("Include is nested, writing content to a buffer");
            task.output
                .get_mut()
                .extend_from_slice(&processed_resp.into_body_bytes());
        }

        Ok(FetchState::Succeeded)
    } else {
        // Response status is NOT success, either continue, fallback to an alt, or fail.
        if let Some(request) = alt {
            debug!("request poll DONE ERROR, trying alt");
            if let Some(fragment) =
                send_fragment_request(request?, None, continue_on_error, dispatch_fragment_request)?
            {
                task.queue.push_front(Element::Include(fragment));
                return Ok(FetchState::Pending);
            }
            debug!("guest returned None, continuing");
            return Ok(FetchState::Succeeded);
        } else if continue_on_error {
            debug!("request poll DONE ERROR, NO ALT, continuing");
            return Ok(FetchState::Succeeded);
        }

        debug!("request poll DONE ERROR, NO ALT, failing");
        Ok(FetchState::Failed(
            request,
            processed_resp.get_status().into(),
        ))
    }
}

// Helper function to write raw content to the client output stream.
// If the depth is 0 and no queue, the content is written directly to the client output stream.
// Otherwise, the content is written to the task's output buffer.
fn process_raw(
    task: &mut Task,
    output_writer: &mut Writer<impl Write>,
    raw: &[u8],
    depth: usize,
) -> Result<()> {
    if depth == 0 && task.output.get_mut().is_empty() {
        debug!("writing previously queued content");
        output_writer
            .get_mut()
            .write_all(raw)
            .map_err(ExecutionError::WriterError)?;
        output_writer.get_mut().flush()?;
    } else {
        trace!("-- Depth: {}", depth);
        debug!(
            "writing blocked content to a queue {:?} ",
            String::from_utf8(raw.to_owned())
        );
        task.output.get_mut().extend_from_slice(raw);
    }
    Ok(())
}

// Helper function to handle the end of a <esi:try> tag
fn process_try(
    task: &mut Task,
    output_writer: &mut Writer<impl Write>,
    attempt_task: &mut Task,
    except_task: &mut Task,
    depth: &mut usize,
    dispatch_fragment_request: &FragmentRequestDispatcher,
    process_fragment_response: Option<&FragmentResponseProcessor>,
) -> Result<()> {
    let attempt_state = fetch_elements(
        depth,
        attempt_task,
        output_writer,
        dispatch_fragment_request,
        process_fragment_response,
    )?;

    let except_state = fetch_elements(
        depth,
        except_task,
        output_writer,
        dispatch_fragment_request,
        process_fragment_response,
    )?;

    trace!("*** Depth: {}", depth);

    match (attempt_state, except_state) {
        (FetchState::Succeeded, _) => {
            task.output
                .get_mut()
                .extend_from_slice(&std::mem::take(attempt_task).output.into_inner());
        }
        (FetchState::Failed(_, _), FetchState::Succeeded) => {
            task.output
                .get_mut()
                .extend_from_slice(&std::mem::take(except_task).output.into_inner());
        }
        (FetchState::Failed(req, res), FetchState::Failed(_req, _res)) => {
            // both tasks failed
            return Err(ExecutionError::UnexpectedStatus(
                req.get_url_str().to_string(),
                res,
            ));
        }
        (FetchState::Pending, _) | (FetchState::Failed(_, _), FetchState::Pending) => {
            // Request are still pending, re-add it to the front of the queue and wait for the next poll.
            task.queue.push_front(Element::Try {
                attempt_task: std::mem::take(attempt_task),
                except_task: std::mem::take(except_task),
            });
        }
    }
    Ok(())
}

// Receives `Event` from the parser and process it.
// The result is pushed to a queue of elements or written to the output stream.
fn event_receiver(
    event: Event,
    queue: &mut VecDeque<Element>,
    is_escaped: bool,
    original_request_metadata: &Request,
    dispatch_fragment_request: &FragmentRequestDispatcher,
    ctx: &mut EvalContext,
) -> Result<()> {
    match event {
        Event::ESI(Tag::Include {
            src,
            alt,
            continue_on_error,
        }) => {
            debug!("Handling <esi:include> tag with src: {}", src);
            // Always interpolate src
            let interpolated_src = try_evaluate_interpolated_string(&src, ctx)?;

            // Always interpolate alt if present
            let interpolated_alt = alt
                .map(|a| try_evaluate_interpolated_string(&a, ctx))
                .transpose()?;
            let req = build_fragment_request(
                original_request_metadata.clone_without_body(),
                &interpolated_src,
                is_escaped,
            );
            let alt_req = interpolated_alt.map(|alt| {
                build_fragment_request(
                    original_request_metadata.clone_without_body(),
                    &alt,
                    is_escaped,
                )
            });
            if let Some(fragment) =
                send_fragment_request(req?, alt_req, continue_on_error, dispatch_fragment_request)?
            {
                // add the pending request to the queue
                queue.push_back(Element::Include(fragment));
            }
        }
        Event::ESI(Tag::Try {
            attempt_events,
            except_events,
        }) => {
            let attempt_task = task_handler(
                attempt_events,
                is_escaped,
                original_request_metadata,
                dispatch_fragment_request,
                ctx,
            )?;
            let except_task = task_handler(
                except_events,
                is_escaped,
                original_request_metadata,
                dispatch_fragment_request,
                ctx,
            )?;

            trace!(
                "*** pushing try content to queue: Attempt - {:?}, Except - {:?}",
                attempt_task.queue,
                except_task.queue
            );
            // push the elements
            queue.push_back(Element::Try {
                attempt_task,
                except_task,
            });
        }
        Event::ESI(Tag::Assign { name, value }) => {
            // TODO: the 'name' here might have a subfield, we need to parse it
            let result = evaluate_expression(&value, ctx)?;
            ctx.set_variable(&name, None, result);
        }
        Event::ESI(Tag::Vars { name }) => {
            debug!("Handling <esi:vars> tag with name: {:?}", name);
            if let Some(name) = name {
                let result = evaluate_expression(&name, ctx)?;
                debug!("Evaluated <esi:vars> result: {:?}", result);
                queue.push_back(Element::Raw(result.to_string().into_bytes()));
            }
        }
        Event::ESI(Tag::When { .. }) => unreachable!(),
        Event::ESI(Tag::Choose {
            when_branches,
            otherwise_events,
        }) => {
            let mut chose_branch = false;
            for (when, events) in when_branches {
                if let Tag::When { test, match_name } = when {
                    if let Some(match_name) = match_name {
                        ctx.set_match_name(&match_name);
                    }
                    let result = evaluate_expression(&test, ctx)?;
                    if result.to_bool() {
                        chose_branch = true;
                        for event in events {
                            event_receiver(
                                event,
                                queue,
                                is_escaped,
                                original_request_metadata,
                                dispatch_fragment_request,
                                ctx,
                            )?;
                        }
                        break;
                    }
                } else {
                    unreachable!()
                }
            }

            if !chose_branch {
                for event in otherwise_events {
                    event_receiver(
                        event,
                        queue,
                        is_escaped,
                        original_request_metadata,
                        dispatch_fragment_request,
                        ctx,
                    )?;
                }
            }
        }

        Event::InterpolatedContent(event) => {
            debug!("Handling interpolated content: {:?}", event);
            let event_str = String::from_utf8(event.iter().copied().collect()).unwrap_or_default();

            process_interpolated_chars(&event_str, ctx, |segment| {
                queue.push_back(Element::Raw(segment.into_bytes()));
                Ok(())
            })?;
        }
        Event::Content(event) => {
            debug!("pushing content to buffer, len: {}", queue.len());
            let mut buf = vec![];
            let mut writer = Writer::new(&mut buf);
            writer.write_event(event)?;
            queue.push_back(Element::Raw(buf));
        }
    }
    Ok(())
}

// Helper function to process a list of events and return a task.
// It's called from `event_receiver` and calls `event_receiver` to process each event in recursion.
fn task_handler(
    events: Vec<Event>,
    is_escaped: bool,
    original_request_metadata: &Request,
    dispatch_fragment_request: &FragmentRequestDispatcher,
    ctx: &mut EvalContext,
) -> Result<Task> {
    let mut task = Task::new();
    for event in events {
        event_receiver(
            event,
            &mut task.queue,
            is_escaped,
            original_request_metadata,
            dispatch_fragment_request,
            ctx,
        )?;
    }
    Ok(task)
}

// Helper function to build a fragment request from a URL
// For HTML content the URL is unescaped if it's escaped (default).
// It can be disabled in the processor configuration for a non-HTML content.
fn build_fragment_request(mut request: Request, url: &str, is_escaped: bool) -> Result<Request> {
    let escaped_url = if is_escaped {
        match quick_xml::escape::unescape(url) {
            Ok(url) => url.to_string(),
            Err(err) => {
                return Err(ExecutionError::InvalidRequestUrl(err.to_string()));
            }
        }
    } else {
        url.to_string()
    };

    if escaped_url.starts_with('/') {
        match Url::parse(
            format!("{}://0.0.0.0{}", request.get_url().scheme(), escaped_url).as_str(),
        ) {
            Ok(u) => {
                request.get_url_mut().set_path(u.path());
                request.get_url_mut().set_query(u.query());
            }
            Err(_err) => {
                return Err(ExecutionError::InvalidRequestUrl(escaped_url));
            }
        };
    } else {
        request.set_url(match Url::parse(&escaped_url) {
            Ok(url) => url,
            Err(_err) => {
                return Err(ExecutionError::InvalidRequestUrl(escaped_url));
            }
        });
    }

    let hostname = request.get_url().host().expect("no host").to_string();

    request.set_header(header::HOST, &hostname);

    Ok(request)
}

fn send_fragment_request(
    req: Request,
    alt: Option<Result<Request>>,
    continue_on_error: bool,
    dispatch_request: &FragmentRequestDispatcher,
) -> Result<Option<Fragment>> {
    debug!("Requesting ESI fragment: {}", req.get_url());

    let request = req.clone_without_body();

    let pending_content: PendingFragmentContent = dispatch_request(req)?;

    Ok(Some(Fragment {
        request,
        alt,
        continue_on_error,
        pending_content,
    }))
}

// Helper function to create an XML reader from a body.
fn reader_from_body(body: Body) -> Reader<Body> {
    let mut reader = Reader::from_reader(body);

    // TODO: make this configurable
    let config = reader.config_mut();
    config.check_end_names = false;

    reader
}

// helper function to drive output to a response stream
fn output_handler(output_writer: &mut Writer<impl Write>, buffer: &[u8]) -> Result<()> {
    output_writer.get_mut().write_all(buffer)?;
    output_writer.get_mut().flush()?;
    Ok(())
}

/// Processes a string containing interpolated expressions using a character-based approach
///
/// This function evaluates expressions like $(HTTP_HOST) in text content and
/// provides the processed segments to the caller through a callback function.
///
/// # Arguments
/// * `input` - The input string containing potential interpolated expressions
/// * `ctx` - Evaluation context containing variables and state
/// * `segment_handler` - A function that handles each segment (raw text or evaluated expression)
///
/// # Returns
/// * `Result<()>` - Success or error during processing
///
pub fn process_interpolated_chars<F>(
    input: &str,
    ctx: &mut EvalContext,
    mut segment_handler: F,
) -> Result<()>
where
    F: FnMut(String) -> Result<()>,
{
    let mut buf = vec![];
    let mut cur = input.chars().peekable();

    while let Some(c) = cur.peek() {
        if *c == '$' {
            let mut new_cur = cur.clone();
            let result = try_evaluate_interpolated(&mut new_cur, ctx);
            match result {
                Some(r) => {
                    // If we have accumulated text, output it first
                    if !buf.is_empty() {
                        segment_handler(buf.into_iter().collect())?;
                        buf = vec![];
                    }

                    // Output the evaluated expression result
                    segment_handler(r.to_string())?;

                    // Update our position
                    cur = new_cur;
                }
                None => {
                    buf.push(cur.next().unwrap());
                }
            }
        } else {
            buf.push(cur.next().unwrap());
        }
    }

    // Output any remaining text
    if !buf.is_empty() {
        segment_handler(buf.into_iter().collect())?;
    }

    Ok(())
}

/// Evaluates all interpolated expressions in a string and returns the complete result
///
/// This is a convenience wrapper around process_interpolated_chars that collects
/// all output into a single string.
///
/// # Arguments
/// * `input` - The input string containing potential interpolated expressions
/// * `ctx` - Evaluation context containing variables and state
///
/// # Returns
/// * `Result<String>` - The fully processed string with all expressions evaluated
///
pub fn try_evaluate_interpolated_string(input: &str, ctx: &mut EvalContext) -> Result<String> {
    let mut result = String::new();

    process_interpolated_chars(input, ctx, |segment| {
        result.push_str(&segment);
        Ok(())
    })?;

    Ok(result)
}
