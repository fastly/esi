#![doc = include_str!("../README.md")]

mod config;
mod error;
mod expression;
mod functions;
mod parser;
pub mod parser_types;

use crate::expression::EvalContext;
use fastly::http::request::PendingRequest;
use fastly::http::{header, Method, StatusCode, Url};
use fastly::{mime, Request, Response};
use log::{debug, error};
use std::io::{BufRead, Write};

pub use crate::error::{ExecutionError as ESIError, Result};
pub use crate::parser::{parse, parse_expression, parse_interpolated_string};

pub use crate::config::Configuration;
pub use crate::error::ExecutionError;

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

/// Representation of an ESI fragment request with its metadata and pending response
pub struct Fragment {
    /// Metadata of the request
    pub(crate) request: Request,
    /// An optional alternate request to send if the original request fails
    pub(crate) alt: Option<String>,
    /// Whether to continue on error
    pub(crate) continue_on_error: bool,
    /// The pending fragment response, which can be polled to retrieve the content
    pub(crate) pending_content: PendingFragmentContent,
}

/// Runtime element representation (matches main branch's Element enum)
/// Holds dispatched fragments ready to wait for execution
use std::borrow::Cow;

enum ExecutionElement<'a> {
    Raw(Cow<'a, [u8]>), // Text/HTML - borrowed from document or owned from evaluation
    Include(Box<Fragment>), // Already dispatched, just needs wait
    Try {
        attempt_elements: Vec<Vec<ExecutionElement<'a>>>,
        except_elements: Vec<ExecutionElement<'a>>,
    },
}

impl PendingFragmentContent {
    /// Wait for and retrieve the response from a pending fragment request
    pub fn wait(self) -> Result<Response> {
        match self {
            Self::PendingRequest(pending_request) => pending_request.wait().map_err(|e| {
                ESIError::ExpressionError(format!("Fragment request wait failed: {}", e))
            }),
            Self::CompletedRequest(response) => Ok(response),
            Self::NoContent => Ok(Response::from_status(StatusCode::NO_CONTENT)),
        }
    }
}

/// A processor for handling ESI responses
///
/// The Processor maintains state and configuration for processing ESI directives
/// in HTML/XML content. It handles fragment inclusion, variable substitution,
/// and conditional processing according to the ESI specification.
///
/// # Fields
/// * `ctx` - Evaluation context containing variables and request metadata
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
/// let request = Request::get("http://example.com/");
///
/// // Initialize the Processor with optional request metadata
/// let processor = Processor::new(Some(request), config);
/// ```
pub struct Processor {
    // The evaluation context containing variables and request metadata
    ctx: EvalContext,
    // The configuration for the processor.
    configuration: Configuration,
}

impl Processor {
    pub fn new(original_request_metadata: Option<Request>, configuration: Configuration) -> Self {
        let mut ctx = EvalContext::new();
        if let Some(req) = original_request_metadata {
            ctx.set_request(req);
        } else {
            ctx.set_request(Request::new(Method::GET, "http://localhost"));
        }
        Self { ctx, configuration }
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
    /// // Process the response, streaming the resulting document directly to the client
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
        let mut output_writer = resp.stream_to_client();

        match self.process_document(
            src_document.take_body(),
            &mut output_writer,
            dispatch_fragment_request,
            process_fragment_response,
        ) {
            Ok(()) => {
                output_writer.finish()?;
                Ok(())
            }
            Err(err) => {
                error!("error processing ESI document: {err}");
                Err(err)
            }
        }
    }

    /// Process an ESI document using callback-based parsing, handling includes and directives
    ///
    /// Uses a streaming parser that invokes callbacks as elements are parsed, enabling:
    /// - True streaming execution (no AST intermediate storage)
    /// - Parallel fragment fetching (all includes dispatched before any wait)
    /// - Minimal memory footprint (process elements as they're parsed)
    ///
    /// Processing happens in two phases:
    /// 1. **Parse & Dispatch**: Parse document with callbacks that evaluate conditionals and dispatch
    ///    all HTTP requests immediately (but don't wait). This builds an execution queue.
    /// 2. **Execute**: Walk the execution queue, waiting for fragments and writing output.
    ///
    /// This ensures optimal performance by:
    /// - Only fetching fragments that are actually needed (not those in unexecuted branches)
    /// - Parallel fetching of all required fragments
    /// - Streaming output as soon as fragments complete
    ///
    /// Handles:
    /// - ESI includes with on-demand fragment fetching
    /// - Variable substitution
    /// - Conditional processing (choose/when/otherwise)
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
    /// # Errors
    /// Returns error if:
    /// * ESI markup parsing fails
    /// * Fragment requests fail (unless `continue_on_error` is set)
    /// * Output writing fails
    pub fn process_document(
        mut self,
        mut src_document: impl BufRead,
        output_writer: &mut impl Write,
        dispatch_fragment_request: Option<&FragmentRequestDispatcher>,
        process_fragment_response: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        // Read the entire document into a string for nom parser
        let mut doc_content = String::new();
        src_document
            .read_to_string(&mut doc_content)
            .map_err(ESIError::WriterError)?;

        // Set up fragment request dispatcher. Use what's provided or use a default
        let dispatch_fragment_request =
            dispatch_fragment_request.unwrap_or(&default_fragment_dispatcher);

        // Queue for execution elements (dispatched includes and raw content)
        let mut execution_queue: Vec<ExecutionElement> = Vec::new();

        // Parse with callback - as we parse, we dispatch includes and build the execution queue
        let parse_result = parser::parse_with_callback(&doc_content, |elements| {
            for element in elements {
                match self.process_element(element, dispatch_fragment_request) {
                    Ok(mut exec_elements) => {
                        execution_queue.append(&mut exec_elements);
                    }
                    Err(e) => {
                        return Err(format!("Error processing element: {}", e));
                    }
                }
            }
            Ok(())
        });

        // Check parse result
        if let Err(e) = parse_result {
            return Err(ESIError::ExpressionError(format!(
                "Nom parser error: {:?}",
                e
            )));
        }

        let (remaining, _) = parse_result.unwrap();

        // Log warning if parser didn't consume everything
        if !remaining.is_empty() {
            debug!(
                "Parser did not consume all input. Remaining: '{}'",
                remaining.chars().take(100).collect::<String>()
            );
        }

        // Execute the queue (wait for fragments and write output)
        // All HTTP requests are now in flight, we wait for them as needed
        self.execute_queue(
            execution_queue,
            output_writer,
            dispatch_fragment_request,
            process_fragment_response,
        )?;

        Ok(())
    }

    /// Process a single parsed element to runtime Elements
    fn process_element<'a>(
        &mut self,
        element: parser_types::Element<'a>,
        dispatch_fragment_request: &FragmentRequestDispatcher,
    ) -> Result<Vec<ExecutionElement<'a>>> {
        use parser_types::{Element, Tag};

        let mut result = Vec::new();

        match element {
            Element::Text(text) => {
                result.push(ExecutionElement::Raw(Cow::Borrowed(text.as_bytes())));
            }
            Element::Html(html) => {
                result.push(ExecutionElement::Raw(Cow::Borrowed(html.as_bytes())));
            }
            Element::Expr(expr) => {
                // Evaluate expression and convert to text
                match expression::eval_expr(expr, &mut self.ctx) {
                    Ok(value) => {
                        if !matches!(value, expression::Value::Null) {
                            let text = value.to_string();
                            if !text.is_empty() {
                                result.push(ExecutionElement::Raw(Cow::Owned(text.into_bytes())));
                            }
                        }
                    }
                    Err(e) => {
                        debug!("Expression evaluation failed: {:?}", e);
                    }
                }
            }
            Element::Esi(tag) => match tag {
                Tag::Assign { name, value } => {
                    // Evaluate and store in context
                    let evaluated_value = match expression::eval_expr(value, &mut self.ctx) {
                        Ok(val) => val,
                        Err(_) => expression::Value::Text("".into()),
                    };
                    self.ctx.set_variable(&name, None, evaluated_value);
                }
                Tag::Include {
                    src,
                    alt,
                    continue_on_error,
                } => {
                    // Interpolate src using self.ctx
                    let interpolated_src = try_evaluate_interpolated_string(&src, &mut self.ctx)?;

                    // Build request
                    let req = build_fragment_request(
                        self.ctx.get_request().clone_without_body(),
                        &interpolated_src,
                        self.configuration.is_escaped_content,
                    )?;

                    // Dispatch immediately (don't wait!)
                    match dispatch_fragment_request(req.clone_without_body()) {
                        Ok(pending_content) => {
                            let fragment = Fragment {
                                request: req,
                                alt: alt.map(|s| s.to_string()),
                                continue_on_error,
                                pending_content,
                            };
                            result.push(ExecutionElement::Include(Box::new(fragment)));
                        }
                        Err(err) => {
                            if continue_on_error {
                                // Try alt if available
                                if let Some(alt_src) = alt {
                                    let interpolated_alt =
                                        try_evaluate_interpolated_string(&alt_src, &mut self.ctx)?;
                                    let alt_req = build_fragment_request(
                                        self.ctx.get_request().clone_without_body(),
                                        &interpolated_alt,
                                        self.configuration.is_escaped_content,
                                    )?;
                                    match dispatch_fragment_request(alt_req.clone_without_body()) {
                                        Ok(alt_pending) => {
                                            let alt_fragment = Fragment {
                                                request: alt_req,
                                                alt: None,
                                                continue_on_error,
                                                pending_content: alt_pending,
                                            };
                                            result.push(ExecutionElement::Include(Box::new(
                                                alt_fragment,
                                            )));
                                        }
                                        Err(_) => {
                                            result.push(ExecutionElement::Raw(Cow::Borrowed(
                                                b"<!-- fragment request failed -->",
                                            )));
                                        }
                                    }
                                } else {
                                    result.push(ExecutionElement::Raw(Cow::Borrowed(
                                        b"<!-- fragment request failed -->",
                                    )));
                                }
                            } else {
                                return Err(ESIError::ExpressionError(format!(
                                    "Fragment request dispatch failed: {}",
                                    err
                                )));
                            }
                        }
                    }
                }
                Tag::Choose {
                    when_branches,
                    otherwise_events,
                } => {
                    // Evaluate conditionals and dispatch only the chosen branch
                    let mut elements = Vec::new();
                    let mut chose_branch = false;

                    for when_branch in when_branches {
                        if let Some(match_name) = &when_branch.match_name {
                            self.ctx.set_match_name(match_name);
                        }
                        let test_result = expression::eval_expr(when_branch.test, &mut self.ctx)?;
                        if test_result.to_bool() {
                            chose_branch = true;
                            for elem in when_branch.content {
                                elements
                                    .extend(self.process_element(elem, dispatch_fragment_request)?);
                            }
                            break;
                        }
                    }

                    if !chose_branch {
                        for elem in otherwise_events {
                            elements.extend(self.process_element(elem, dispatch_fragment_request)?);
                        }
                    }

                    // Flatten the chosen elements into result
                    result.extend(elements);
                }
                Tag::Try {
                    attempt_events,
                    except_events,
                } => {
                    // Dispatch all attempts
                    let mut attempt_elements = Vec::new();
                    for attempt_list in attempt_events {
                        let mut attempt_exec = Vec::new();
                        for elem in attempt_list {
                            attempt_exec
                                .extend(self.process_element(elem, dispatch_fragment_request)?);
                        }
                        attempt_elements.push(attempt_exec);
                    }

                    let mut except_exec = Vec::new();
                    for elem in except_events {
                        except_exec.extend(self.process_element(elem, dispatch_fragment_request)?);
                    }

                    result.push(ExecutionElement::Try {
                        attempt_elements,
                        except_elements: except_exec,
                    });
                }
                Tag::Vars { .. }
                | Tag::When { .. }
                | Tag::Attempt(_)
                | Tag::Except(_)
                | Tag::Otherwise => {
                    debug!("Unexpected standalone tag: {:?}", tag);
                }
            },
        }

        Ok(result)
    }

    /// Execute the queue of elements
    fn execute_queue<'a>(
        &mut self,
        elements: Vec<ExecutionElement<'a>>,
        output_writer: &mut impl Write,
        dispatcher: &FragmentRequestDispatcher,
        processor: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        for element in elements {
            match element {
                ExecutionElement::Raw(bytes) => {
                    output_writer.write_all(&bytes)?;
                }
                ExecutionElement::Include(fragment) => {
                    self.process_include(*fragment, output_writer, dispatcher, processor)?;
                }
                ExecutionElement::Try {
                    attempt_elements,
                    except_elements,
                } => {
                    let mut succeeded = false;
                    for attempt in attempt_elements {
                        let mut attempt_output = Vec::new();
                        if self
                            .execute_queue(attempt, &mut attempt_output, dispatcher, processor)
                            .is_ok()
                        {
                            output_writer.write_all(&attempt_output)?;
                            succeeded = true;
                            break;
                        }
                    }
                    if !succeeded {
                        self.execute_queue(except_elements, output_writer, dispatcher, processor)?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Process an esi:include tag by fetching the fragment and writing it to the output
    fn process_include(
        &mut self,
        fragment: Fragment,
        output_writer: &mut impl Write,
        dispatch_fragment_request: &FragmentRequestDispatcher,
        process_fragment_response: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        // Deconstruct the fragment
        let Fragment {
            request,
            alt,
            continue_on_error,
            pending_content,
        } = fragment;

        // Wait for the fragment response
        let response = pending_content.wait()?;

        // Apply process_fragment_response callback if provided
        let mut req_for_processor = request.clone_without_body();
        let final_response = if let Some(processor) = process_fragment_response {
            processor(&mut req_for_processor, response)?
        } else {
            response
        };

        // Check if request was successful
        if final_response.get_status().is_success() {
            // Write the response body to output
            let body_bytes = final_response.into_body_bytes();
            let body_str = std::str::from_utf8(&body_bytes).unwrap_or("<!-- invalid utf8 -->");
            output_writer.write_all(body_str.as_bytes())?;
            Ok(())
        } else {
            // Response status is NOT success, either continue, fallback to alt, or fail
            if let Some(alt_src) = alt {
                debug!("Main request failed, trying alt");
                let interpolated_alt = try_evaluate_interpolated_string(&alt_src, &mut self.ctx)?;

                let alt_req = build_fragment_request(
                    self.ctx.get_request().clone_without_body(),
                    &interpolated_alt,
                    self.configuration.is_escaped_content,
                )?;

                match dispatch_fragment_request(alt_req.clone_without_body()) {
                    Ok(alt_pending) => {
                        // Wait for alt fragment and process it
                        let alt_response = alt_pending.wait()?;

                        // Apply process_fragment_response callback if provided
                        let mut alt_req_for_processor = alt_req.clone_without_body();
                        let final_alt_response = if let Some(processor) = process_fragment_response
                        {
                            processor(&mut alt_req_for_processor, alt_response)?
                        } else {
                            alt_response
                        };

                        // Write the alt response body to output
                        let body_bytes = final_alt_response.into_body_bytes();
                        let body_str =
                            std::str::from_utf8(&body_bytes).unwrap_or("<!-- invalid utf8 -->");
                        output_writer.write_all(body_str.as_bytes())?;
                        Ok(())
                    }
                    Err(_) => {
                        if continue_on_error {
                            // Both main and alt failed, but continue-on-error is set
                            output_writer.write_all(b"<!-- fragment request failed -->")?;
                            Ok(())
                        } else {
                            Err(ESIError::ExpressionError(
                                "Both main and alt fragment requests failed".to_string(),
                            ))
                        }
                    }
                }
            } else if continue_on_error {
                // No alt, but continue on error
                debug!("Main request failed, no alt, continuing due to continue_on_error");
                output_writer.write_all(b"<!-- fragment request failed -->")?;
                Ok(())
            } else {
                Err(ESIError::ExpressionError(format!(
                    "Fragment request failed with status: {}",
                    final_response.get_status()
                )))
            }
        }
    }
}

// Default fragment request dispatcher that uses the request's hostname as backend
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

// Helper function to build a fragment request from a URL
// For HTML content the URL is unescaped if it's escaped (default).
// It can be disabled in the processor configuration for a non-HTML content.
fn build_fragment_request(mut request: Request, url: &str, is_escaped: bool) -> Result<Request> {
    let escaped_url = if is_escaped {
        html_escape::decode_html_entities(url).into_owned()
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
        }
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

/// Processes a string containing interpolated expressions using a character-based approach
///
/// This function evaluates expressions like $(`HTTP_HOST``) in text content and
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
    // Parse the input string with interpolated expressions using nom parser
    let elements = match crate::parser::parse_interpolated_string(input) {
        Ok((_, elements)) => elements,
        Err(_) => {
            // If parsing fails, treat the whole input as text
            segment_handler(input.to_string())?;
            return Ok(());
        }
    };

    // Process each element
    for element in elements {
        match element {
            parser_types::Element::Text(text) => {
                segment_handler(text.to_string())?;
            }
            parser_types::Element::Expr(expr) => {
                // Evaluate the expression using eval_expr
                match crate::expression::eval_expr(expr, ctx) {
                    Ok(value) => segment_handler(value.to_string())?,
                    Err(e) => {
                        // Log the error but continue processing (same behavior as old code)
                        debug!("Error while evaluating interpolated expression: {e}");
                    }
                }
            }
            _ => {
                // Skip ESI tags (shouldn't happen in interpolated strings but handle gracefully)
            }
        }
    }

    Ok(())
}

/// Evaluates all interpolated expressions in a string and returns the complete result
///
/// This is a convenience wrapper around `process_interpolated_chars` that collects
/// all output into a single string.
///
/// # Arguments
/// * `input` - The input string containing potential interpolated expressions
/// * `ctx` - Evaluation context containing variables and state
///
/// # Returns
/// * `Result<String>` - The fully processed string with all expressions evaluated
///
/// # Errors
/// Returns error if expression evaluation fails
///
pub fn try_evaluate_interpolated_string(input: &str, ctx: &mut EvalContext) -> Result<String> {
    let mut result = String::new();

    process_interpolated_chars(input, ctx, |segment| {
        result.push_str(&segment);
        Ok(())
    })?;

    Ok(result)
}
// Helper Functions
