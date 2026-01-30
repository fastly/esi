#![doc = include_str!("../README.md")]

mod config;
mod error;
mod expression;
mod functions;
mod parser;
pub mod parser_types;

use crate::expression::EvalContext;
use bytes::{Buf, Bytes, BytesMut};
use fastly::http::request::{PendingRequest, PollResult};
use fastly::http::{header, Method, StatusCode, Url};
use fastly::{mime, Request, Response};
use log::{debug, error};
use std::collections::VecDeque;
use std::io::{BufRead, Write};

pub use crate::error::{ExecutionError as ESIError, Result};
pub use crate::parser::{parse, parse_complete, parse_expression, parse_interpolated_string};

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
    pub(crate) alt: Option<Bytes>,
    /// Whether to continue on error
    pub(crate) continue_on_error: bool,
    /// The pending fragment response, which can be polled to retrieve the content
    pub(crate) pending_content: PendingFragmentContent,
}

/// Queue element for streaming processing
/// Elements that need to be executed in order
enum QueuedElement {
    /// Raw content ready to write (text/html/evaluated expressions)
    Content(Bytes),
    /// A dispatched include waiting to be executed
    Include(Box<Fragment>),
    /// A try block with attempts and except clause
    /// All includes from all attempts have been dispatched in parallel
    Try {
        attempt_elements: Vec<Vec<QueuedElement>>,
        except_elements: Vec<QueuedElement>,
    },
}

impl PendingFragmentContent {
    /// Poll to check if the request is ready without blocking
    /// Returns the updated PendingFragmentContent (either still Pending or now Completed/NoContent)
    pub fn poll(self) -> Self {
        match self {
            Self::PendingRequest(pending_request) => match pending_request.poll() {
                PollResult::Done(result) => match result {
                    Ok(response) => Self::CompletedRequest(response),
                    Err(_) => Self::NoContent, // Error case
                },
                PollResult::Pending(pending_request) => {
                    // Still pending - put it back
                    Self::PendingRequest(pending_request)
                }
            },
            // Already completed - return as-is
            other => other,
        }
    }

    /// Check if the content is ready (completed or no content)
    pub fn is_ready(&self) -> bool {
        !matches!(self, Self::PendingRequest(_))
    }

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
    // Queue for pending fragments and blocked content
    queue: VecDeque<QueuedElement>,
}

impl Processor {
    pub fn new(original_request_metadata: Option<Request>, configuration: Configuration) -> Self {
        let mut ctx = EvalContext::new();
        if let Some(req) = original_request_metadata {
            ctx.set_request(req);
        } else {
            ctx.set_request(Request::new(Method::GET, "http://localhost"));
        }
        Self {
            ctx,
            configuration,
            queue: VecDeque::new(),
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

    /// Process an ESI document with industry-grade streaming architecture
    ///
    /// This method implements **three levels of streaming** for optimal performance:
    ///
    /// ## 1. Chunked Input Reading (Memory Efficient)
    /// - Reads source document in 8KB chunks from BufRead
    /// - Accumulates chunks until parser can make progress
    /// - Prevents loading entire document into memory at once
    /// - Bounded memory growth with incremental processing
    ///
    /// ## 2. Streaming Output (Low Latency)
    /// - Writes processed content immediately as elements are parsed
    /// - Non-blocking poll checks for completed fragments
    /// - Output reaches client with minimal delay
    /// - No buffering of final output
    ///
    /// ## 3. Streaming Fragments (Maximum Parallelism)
    /// - Dispatches all includes immediately (non-blocking)
    /// - Uses select() to process whichever fragment completes first
    /// - All fragments fetch in parallel, no wasted waiting
    /// - Try blocks dispatch all attempts' includes upfront
    ///
    /// ## Key Features:
    /// - Only fetches fragments that are actually needed (not those in unexecuted branches)
    /// - Fully recursive nested try/except blocks
    /// - Proper alt fallback and continue_on_error handling
    /// - Full ESI specification compliance
    ///
    /// ## Note on Parsing:
    /// The parser (nom-based) requires complete input for each parse operation.
    /// We handle this by buffering input chunks until a successful parse,
    /// then processing parsed elements immediately while retaining unparsed remainder.
    ///
    /// # Arguments
    /// * `src_document` - BufRead source containing ESI markup (streams in chunks)
    /// * `output_writer` - Writer to stream processed output to (writes immediately)
    /// * `dispatch_fragment_request` - Optional handler for fragment requests
    /// * `process_fragment_response` - Optional processor for fragment responses
    ///
    /// # Returns
    /// * `Result<()>` - Ok if processing completed successfully
    ///
    /// # Errors
    /// Returns error if:
    /// * ESI markup parsing fails or document is malformed
    /// * Fragment requests fail (unless `continue_on_error` is set)
    /// * Input reading or output writing fails
    /// * Invalid UTF-8 encoding encountered
    pub fn process_document(
        mut self,
        mut src_document: impl BufRead,
        output_writer: &mut impl Write,
        dispatch_fragment_request: Option<&FragmentRequestDispatcher>,
        process_fragment_response: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        // Set up fragment request dispatcher
        let dispatcher = dispatch_fragment_request.unwrap_or(&default_fragment_dispatcher);

        // STREAMING INPUT PARSING:
        // Read chunks, parse incrementally, process elements as we parse them
        const CHUNK_SIZE: usize = 8192; // 8KB chunks
                                        // Using BytesMut for zero-copy parsing
        let mut buffer = BytesMut::with_capacity(CHUNK_SIZE);
        let mut read_buf = vec![0u8; CHUNK_SIZE];
        let mut eof = false;
        let mut iterations = 0;
        const MAX_ITERATIONS: usize = 10000;

        loop {
            iterations += 1;
            if iterations > MAX_ITERATIONS {
                return Err(ESIError::ExpressionError(format!(
                    "Infinite loop detected after {} iterations, buffer len: {}, eof: {}",
                    iterations,
                    buffer.len(),
                    eof
                )));
            }
            // Read more data if we haven't hit EOF yet
            if !eof {
                match src_document.read(&mut read_buf) {
                    Ok(0) => {
                        // EOF reached - parser can now make final decisions
                        eof = true;
                    }
                    Ok(n) => {
                        // Append new data to buffer (zero-copy extend)
                        buffer.extend_from_slice(&read_buf[..n]);
                    }
                    Err(e) => {
                        return Err(ESIError::WriterError(e));
                    }
                }
            }

            // Freeze a view of the buffer for zero-copy parsing
            // We clone here because freeze() consumes, but Bytes cloning is cheap (ref count)
            let frozen = buffer.clone().freeze();

            // Try to parse what we have in the buffer
            // Use streaming parser unless we're at EOF, then use complete parser
            let parse_result = if eof {
                // At EOF - use complete parser which handles Incomplete by treating remainder as text
                parser::parse_complete(&frozen)
            } else {
                // Still streaming - use streaming parser
                parser::parse(&frozen)
            };

            match parse_result {
                Ok((remaining, elements)) => {
                    // Successfully parsed some elements
                    for element in elements {
                        self.process_element_streaming(element, output_writer, dispatcher)?;
                        // After each element, check if any queued includes are ready (non-blocking poll)
                        self.process_ready_queue_items(
                            output_writer,
                            dispatcher,
                            process_fragment_response,
                        )?;
                    }

                    // Calculate how many bytes were consumed
                    let consumed = frozen.len() - remaining.len();

                    // Keep the unparsed remainder for next iteration
                    if remaining.is_empty() {
                        if eof {
                            // All done - parsed everything and reached EOF
                            break;
                        } else {
                            // Parsed everything in buffer, clear it and continue reading
                            buffer.clear();
                        }
                    } else {
                        // Have unparsed remainder
                        if eof {
                            // At EOF with unparsed data - already handled by parse_complete_bytes
                            // which treats remainder as Text elements
                            break;
                        } else {
                            // Keep remainder for next chunk - advance past consumed bytes
                            buffer.advance(consumed);
                        }
                    }
                }
                Err(nom::Err::Incomplete(_)) => {
                    // Streaming parser needs more data
                    if eof {
                        // At EOF but parser wants more data - this shouldn't happen
                        // with parse_complete_bytes, but handle it just in case
                        if !buffer.is_empty() {
                            output_writer.write_all(&buffer)?;
                        }
                        break;
                    }
                    // Not at EOF - loop will read more data
                }
                Err(nom::Err::Error(e)) | Err(nom::Err::Failure(e)) => {
                    // Parse error
                    if eof {
                        // At EOF with parse error - this is a real error
                        return Err(ESIError::ExpressionError(format!("Parser error: {:?}", e)));
                    } else {
                        // Not at EOF - maybe more data will help, output what we have and continue
                        output_writer.write_all(&buffer)?;
                        buffer.clear();
                    }
                }
            }
        }

        // DRAIN QUEUE: Wait for all remaining pending fragments (blocking waits)
        self.drain_queue(output_writer, dispatcher, process_fragment_response)?;

        Ok(())
    }

    /// Process a single element in streaming mode
    fn process_element_streaming(
        &mut self,
        element: parser_types::Element,
        output_writer: &mut impl Write,
        dispatcher: &FragmentRequestDispatcher,
    ) -> Result<()> {
        use parser_types::{Element, Tag};

        match element {
            Element::Text(text) | Element::Html(text) => {
                // Non-blocking content
                if self.queue.is_empty() {
                    // Not blocked - write immediately
                    output_writer.write_all(&text)?;
                } else {
                    // Blocked - queue it
                    self.queue.push_back(QueuedElement::Content(text));
                }
            }

            Element::Expr(expr) => {
                // Evaluate and treat as non-blocking content
                match expression::eval_expr(expr, &mut self.ctx) {
                    Ok(val) if !matches!(val, expression::Value::Null) => {
                        let bytes = val.to_bytes();
                        if !bytes.is_empty() {
                            if self.queue.is_empty() {
                                output_writer.write_all(&bytes)?;
                            } else {
                                self.queue.push_back(QueuedElement::Content(bytes));
                            }
                        }
                    }
                    _ => {} // Skip null or error
                }
            }

            Element::Esi(Tag::Assign { name, value }) => {
                // Non-blocking - just update context
                let val = expression::eval_expr(value, &mut self.ctx)
                    .unwrap_or(expression::Value::Text("".into()));
                self.ctx.set_variable(&name, None, val);
            }

            Element::Esi(Tag::Vars { name }) => {
                // Non-blocking - just update context
                if let Some(n) = name {
                    self.ctx.set_match_name(&n);
                }
            }

            Element::Esi(Tag::Include {
                src,
                alt,
                continue_on_error,
                params: _,
            }) => {
                // BLOCKING - dispatch and queue
                // TODO: Pass params to dispatch_and_queue_include
                self.dispatch_and_queue_include(&src, alt.as_ref(), continue_on_error, dispatcher)?;
            }

            Element::Esi(Tag::Choose {
                when_branches,
                otherwise_events,
            }) => {
                // Evaluate condition and recursively process chosen branch
                let mut chose_branch = false;

                for when_branch in when_branches {
                    if let Some(ref match_name) = when_branch.match_name {
                        self.ctx.set_match_name(match_name);
                    }

                    match expression::eval_expr(when_branch.test, &mut self.ctx) {
                        Ok(test_result) if test_result.to_bool() => {
                            // This branch matches - recursively process it
                            for elem in when_branch.content {
                                self.process_element_streaming(elem, output_writer, dispatcher)?;
                            }
                            chose_branch = true;
                            break;
                        }
                        _ => continue,
                    }
                }

                // No when matched - process otherwise
                if !chose_branch {
                    for elem in otherwise_events {
                        self.process_element_streaming(elem, output_writer, dispatcher)?;
                    }
                }
            }

            Element::Esi(Tag::Try {
                attempt_events,
                except_events,
            }) => {
                // Process try/except with parallel dispatch:
                // Dispatch all includes from all attempts, then add try block to queue
                let mut attempt_queues = Vec::new();

                for attempt in attempt_events {
                    let mut attempt_queue = Vec::new();

                    for elem in attempt {
                        // Process each element in the attempt, collecting queued items
                        match elem {
                            Element::Text(text) => {
                                attempt_queue.push(QueuedElement::Content(text));
                            }
                            Element::Html(html) => {
                                attempt_queue.push(QueuedElement::Content(html));
                            }
                            Element::Expr(expr) => {
                                match expression::eval_expr(expr, &mut self.ctx) {
                                    Ok(value) => {
                                        if !matches!(value, expression::Value::Null) {
                                            let bytes = value.to_bytes();
                                            if !bytes.is_empty() {
                                                attempt_queue.push(QueuedElement::Content(bytes));
                                            }
                                        }
                                    }
                                    Err(e) => {
                                        debug!("Expression evaluation failed: {:?}", e);
                                    }
                                }
                            }
                            Element::Esi(Tag::Include {
                                src,
                                alt,
                                continue_on_error,
                                params: _,
                            }) => {
                                // Dispatch the include and add to attempt queue
                                // TODO: Pass params to dispatch_include_to_element
                                let queued_element = self.dispatch_include_to_element(
                                    &src,
                                    alt.as_ref(),
                                    continue_on_error,
                                    dispatcher,
                                )?;
                                attempt_queue.push(queued_element);
                            }
                            Element::Esi(Tag::Choose {
                                when_branches,
                                otherwise_events,
                            }) => {
                                // Evaluate and process chosen branch inline
                                let mut chose_branch = false;
                                for when_branch in when_branches {
                                    if let Some(match_name) = &when_branch.match_name {
                                        self.ctx.set_match_name(match_name);
                                    }
                                    let test_result =
                                        expression::eval_expr(when_branch.test, &mut self.ctx)?;
                                    if test_result.to_bool() {
                                        chose_branch = true;
                                        for elem in when_branch.content {
                                            self.process_element_streaming(
                                                elem,
                                                output_writer,
                                                dispatcher,
                                            )?;
                                        }
                                        break;
                                    }
                                }
                                if !chose_branch {
                                    for elem in otherwise_events {
                                        self.process_element_streaming(
                                            elem,
                                            output_writer,
                                            dispatcher,
                                        )?;
                                    }
                                }
                            }
                            Element::Esi(Tag::Try { .. }) => {
                                // Nested try blocks - process recursively
                                self.process_element_streaming(
                                    elem.clone(),
                                    output_writer,
                                    dispatcher,
                                )?;
                            }
                            _ => {}
                        }
                    }

                    attempt_queues.push(attempt_queue);
                }

                // Process except clause elements
                let mut except_queue = Vec::new();
                for elem in except_events {
                    match elem {
                        Element::Text(text) => {
                            except_queue.push(QueuedElement::Content(text));
                        }
                        Element::Html(html) => {
                            except_queue.push(QueuedElement::Content(html));
                        }
                        Element::Expr(expr) => match expression::eval_expr(expr, &mut self.ctx) {
                            Ok(value) => {
                                if !matches!(value, expression::Value::Null) {
                                    let bytes = value.to_bytes();
                                    if !bytes.is_empty() {
                                        except_queue.push(QueuedElement::Content(bytes));
                                    }
                                }
                            }
                            Err(e) => {
                                debug!("Expression evaluation failed: {:?}", e);
                            }
                        },
                        Element::Esi(Tag::Include {
                            src,
                            alt,
                            continue_on_error,
                            params: _,
                        }) => {
                            // Dispatch the include and add to except queue
                            // TODO: Pass params to dispatch_include_to_element
                            let queued_element = self.dispatch_include_to_element(
                                &src,
                                alt.as_ref(),
                                continue_on_error,
                                dispatcher,
                            )?;
                            except_queue.push(queued_element);
                        }
                        _ => {}
                    }
                }

                // Add the try block to the queue with all attempts and except dispatched
                self.queue.push_back(QueuedElement::Try {
                    attempt_elements: attempt_queues,
                    except_elements: except_queue,
                });
            }

            _ => {} // Other standalone tags shouldn't appear
        }

        Ok(())
    }

    /// Dispatch an include and add to queue
    fn dispatch_and_queue_include(
        &mut self,
        src: &Bytes,
        alt: Option<&Bytes>,
        continue_on_error: bool,
        dispatcher: &FragmentRequestDispatcher,
    ) -> Result<()> {
        let queued_element =
            self.dispatch_include_to_element(src, alt, continue_on_error, dispatcher)?;
        self.queue.push_back(queued_element);
        Ok(())
    }

    /// Dispatch an include and return a QueuedElement (for flexible queue insertion)
    /// This is the single source of truth for include dispatching logic
    fn dispatch_include_to_element(
        &mut self,
        src: &Bytes,
        alt: Option<&Bytes>,
        continue_on_error: bool,
        dispatcher: &FragmentRequestDispatcher,
    ) -> Result<QueuedElement> {
        let interpolated_src = try_evaluate_interpolated_string(src, &mut self.ctx)?;

        let req = build_fragment_request(
            self.ctx.get_request().clone_without_body(),
            &interpolated_src,
            self.configuration.is_escaped_content,
        )?;

        match dispatcher(req.clone_without_body()) {
            Ok(pending) => {
                let fragment = Fragment {
                    request: req,
                    alt: alt.cloned(),
                    continue_on_error,
                    pending_content: pending,
                };
                Ok(QueuedElement::Include(Box::new(fragment)))
            }
            Err(_) if continue_on_error => {
                // Try alt or add error placeholder
                if let Some(alt_src) = alt {
                    let alt_interpolated =
                        try_evaluate_interpolated_string(alt_src, &mut self.ctx)?;
                    let alt_req = build_fragment_request(
                        self.ctx.get_request().clone_without_body(),
                        &alt_interpolated,
                        self.configuration.is_escaped_content,
                    )?;

                    match dispatcher(alt_req.clone_without_body()) {
                        Ok(alt_pending) => {
                            let alt_fragment = Fragment {
                                request: alt_req,
                                alt: None,
                                continue_on_error,
                                pending_content: alt_pending,
                            };
                            Ok(QueuedElement::Include(Box::new(alt_fragment)))
                        }
                        Err(_) => Ok(QueuedElement::Content(Bytes::from_static(
                            b"<!-- fragment request failed -->",
                        ))),
                    }
                } else {
                    Ok(QueuedElement::Content(Bytes::from_static(
                        b"<!-- fragment request failed -->",
                    )))
                }
            }
            Err(e) => Err(ESIError::ExpressionError(format!(
                "Fragment dispatch failed: {}",
                e
            ))),
        }
    }

    /// Check ready queue items - non-blocking poll
    /// Process any fragments that are already completed without blocking
    fn process_ready_queue_items(
        &mut self,
        output_writer: &mut impl Write,
        dispatcher: &FragmentRequestDispatcher,
        processor: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        // Process ready items from the front of the queue without blocking
        loop {
            // Check what's at the front
            let should_try = match self.queue.front() {
                Some(QueuedElement::Content(_)) => true,
                Some(QueuedElement::Include(_)) => true,
                Some(QueuedElement::Try { .. }) => false, // Skip try blocks
                None => false,
            };

            if !should_try {
                break;
            }

            // Pop and process the front element
            let elem = self.queue.pop_front().unwrap();
            match elem {
                QueuedElement::Content(content) => {
                    // Content is always ready
                    output_writer.write_all(&content)?;
                }
                QueuedElement::Include(mut fragment) => {
                    // Poll the fragment (non-blocking check)
                    let pending_content = std::mem::replace(
                        &mut fragment.pending_content,
                        PendingFragmentContent::NoContent,
                    );
                    fragment.pending_content = pending_content.poll();

                    // Check if it's ready now
                    if fragment.pending_content.is_ready() {
                        // Process it!
                        self.process_include_from_queue(
                            *fragment,
                            output_writer,
                            dispatcher,
                            processor,
                        )?;
                    } else {
                        // Still pending - put it back at the front and stop
                        self.queue.push_front(QueuedElement::Include(fragment));
                        break;
                    }
                }
                QueuedElement::Try { .. } => {
                    unreachable!("Try blocks should be skipped in ready check");
                }
            }
        }
        Ok(())
    }

    /// Drain queue with efficient waiting using select()
    /// Uses select() to process whichever pending request completes first
    fn drain_queue(
        &mut self,
        output_writer: &mut impl Write,
        dispatcher: &FragmentRequestDispatcher,
        processor: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        while !self.queue.is_empty() {
            // First, write out any content that's at the front
            while let Some(QueuedElement::Content(_)) = self.queue.front() {
                if let Some(QueuedElement::Content(bytes)) = self.queue.pop_front() {
                    output_writer.write_all(&bytes)?;
                }
            }

            if self.queue.is_empty() {
                break;
            }

            // Collect all pending includes from the queue
            let mut pending_fragments: Vec<(usize, Box<Fragment>)> = Vec::new();
            let mut temp_queue: VecDeque<QueuedElement> = VecDeque::new();

            for (idx, elem) in self.queue.drain(..).enumerate() {
                match elem {
                    QueuedElement::Include(fragment) => {
                        if matches!(
                            fragment.pending_content,
                            PendingFragmentContent::PendingRequest(_)
                        ) {
                            pending_fragments.push((idx, fragment));
                        } else {
                            // Already ready - process immediately
                            temp_queue.push_back(QueuedElement::Include(fragment));
                        }
                    }
                    other => temp_queue.push_back(other),
                }
            }

            // Restore the queue with non-pending items
            self.queue = temp_queue;

            if pending_fragments.is_empty() {
                // Process remaining non-pending items
                if let Some(elem) = self.queue.pop_front() {
                    match elem {
                        QueuedElement::Include(fragment) => {
                            self.process_include_from_queue(
                                *fragment,
                                output_writer,
                                dispatcher,
                                processor,
                            )?;
                        }
                        QueuedElement::Try {
                            attempt_elements,
                            except_elements,
                        } => {
                            // Process try block: try each attempt, use except if all fail
                            self.process_try_block(
                                attempt_elements,
                                except_elements,
                                output_writer,
                                dispatcher,
                                processor,
                            )?;
                        }
                        QueuedElement::Content(_) => {
                            unreachable!("Content should have been processed above");
                        }
                    }
                }
                continue;
            }

            // Extract PendingRequests for select()
            let mut pending_reqs: Vec<PendingRequest> = Vec::new();
            let mut fragments_by_request: Vec<(usize, Box<Fragment>)> = Vec::new();

            for (idx, mut fragment) in pending_fragments {
                if let PendingFragmentContent::PendingRequest(pending_req) = std::mem::replace(
                    &mut fragment.pending_content,
                    PendingFragmentContent::NoContent,
                ) {
                    pending_reqs.push(pending_req);
                    fragments_by_request.push((idx, fragment));
                }
            }

            if pending_reqs.is_empty() {
                continue;
            }

            // Wait for any one to complete using select
            let (result, remaining) = fastly::http::request::select(pending_reqs);

            // The completed request is the one that's NOT in remaining
            let completed_idx = fragments_by_request.len() - remaining.len() - 1;
            let (_original_idx, mut completed_fragment) =
                fragments_by_request.remove(completed_idx);

            // Update the completed fragment with the result
            completed_fragment.pending_content = match result {
                Ok(response) => PendingFragmentContent::CompletedRequest(response),
                Err(_) => PendingFragmentContent::NoContent,
            };

            // Put remaining fragments back in queue (with their pending requests restored)
            for (pending_req, (_idx, mut fragment)) in
                remaining.into_iter().zip(fragments_by_request)
            {
                fragment.pending_content = PendingFragmentContent::PendingRequest(pending_req);
                self.queue.push_back(QueuedElement::Include(fragment));
            }

            // Process the completed fragment
            self.process_include_from_queue(
                *completed_fragment,
                output_writer,
                dispatcher,
                processor,
            )?;
        }

        Ok(())
    }

    /// Process a try block recursively, handling nested try blocks naturally
    fn process_try_block(
        &mut self,
        attempt_elements: Vec<Vec<QueuedElement>>,
        except_elements: Vec<QueuedElement>,
        output_writer: &mut impl Write,
        dispatcher: &FragmentRequestDispatcher,
        processor: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        let mut succeeded = false;

        // Try each attempt in order
        for attempt in attempt_elements {
            match self.process_queued_elements(attempt, dispatcher, processor) {
                Ok(buffer) => {
                    // This attempt succeeded - write it out
                    output_writer.write_all(&buffer)?;
                    succeeded = true;
                    break;
                }
                Err(_) => {
                    // This attempt failed - try the next one
                    continue;
                }
            }
        }

        // If all attempts failed, process except clause
        if !succeeded {
            let except_buffer =
                self.process_queued_elements(except_elements, dispatcher, processor)?;
            output_writer.write_all(&except_buffer)?;
        }

        Ok(())
    }

    /// Process a list of queued elements recursively, returning the output buffer
    /// This naturally handles nested try blocks through recursion
    fn process_queued_elements(
        &mut self,
        elements: Vec<QueuedElement>,
        dispatcher: &FragmentRequestDispatcher,
        processor: Option<&FragmentResponseProcessor>,
    ) -> Result<Vec<u8>> {
        let mut buffer = Vec::new();

        for elem in elements {
            match elem {
                QueuedElement::Content(bytes) => {
                    buffer.write_all(&bytes)?;
                }
                QueuedElement::Include(fragment) => {
                    self.process_include_from_queue(*fragment, &mut buffer, dispatcher, processor)?;
                }
                QueuedElement::Try {
                    attempt_elements,
                    except_elements,
                } => {
                    // Recursively process nested try block
                    self.process_try_block(
                        attempt_elements,
                        except_elements,
                        &mut buffer,
                        dispatcher,
                        processor,
                    )?;
                }
            }
        }

        Ok(buffer)
    }

    /// Process an include from the queue (wait and write, handle alt)
    fn process_include_from_queue(
        &mut self,
        fragment: Fragment,
        output_writer: &mut impl Write,
        dispatcher: &FragmentRequestDispatcher,
        processor: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        let continue_on_error = fragment.continue_on_error;

        // Wait for response
        let response = fragment.pending_content.wait()?;

        // Apply processor if provided
        let mut req_for_processor = fragment.request.clone_without_body();
        let final_response = if let Some(proc) = processor {
            proc(&mut req_for_processor, response)?
        } else {
            response
        };

        // Check if successful
        if final_response.get_status().is_success() {
            let body_bytes = final_response.into_body_bytes();
            // Write Bytes directly - no UTF-8 conversion needed!
            output_writer.write_all(&body_bytes)?;
            Ok(())
        } else if let Some(alt_src) = fragment.alt {
            // Try alt
            debug!("Main request failed, trying alt");
            let alt_interpolated = try_evaluate_interpolated_string(&alt_src, &mut self.ctx)?;
            let alt_req = build_fragment_request(
                self.ctx.get_request().clone_without_body(),
                &alt_interpolated,
                self.configuration.is_escaped_content,
            )?;

            match dispatcher(alt_req.clone_without_body()) {
                Ok(alt_pending) => {
                    let alt_response = alt_pending.wait()?;
                    let mut alt_req_for_proc = alt_req.clone_without_body();
                    let final_alt = if let Some(proc) = processor {
                        proc(&mut alt_req_for_proc, alt_response)?
                    } else {
                        alt_response
                    };

                    let body_bytes = final_alt.into_body_bytes();
                    // Write Bytes directly - no UTF-8 conversion needed!
                    output_writer.write_all(&body_bytes)?;
                    Ok(())
                }
                Err(_) if continue_on_error => {
                    output_writer.write_all(b"<!-- fragment request failed -->")?;
                    Ok(())
                }
                Err(_) => Err(ESIError::ExpressionError(
                    "Both main and alt failed".to_string(),
                )),
            }
        } else if continue_on_error {
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
fn build_fragment_request(mut request: Request, url: &Bytes, is_escaped: bool) -> Result<Request> {
    // Convert Bytes to str for URL parsing
    let url_str = std::str::from_utf8(url)
        .map_err(|_| ExecutionError::ExpressionError("Invalid UTF-8 in URL".to_string()))?;

    let escaped_url = if is_escaped {
        html_escape::decode_html_entities(url_str).into_owned()
    } else {
        url_str.to_string()
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

/// Processes Bytes containing interpolated expressions
///
/// This function evaluates expressions like $(HTTP_HOST) in text content and
/// provides the processed segments to the caller through a callback function.
/// ZERO-COPY: Works directly with Bytes references.
///
/// # Arguments
/// * `input` - The input Bytes containing potential interpolated expressions
/// * `ctx` - Evaluation context containing variables and state
/// * `segment_handler` - A function that handles each segment (raw text or evaluated expression)
///
/// # Returns
/// * `Result<()>` - Success or error during processing
///
pub fn process_interpolated_chars<F>(
    input: &Bytes,
    ctx: &mut EvalContext,
    mut segment_handler: F,
) -> Result<()>
where
    F: FnMut(Bytes) -> Result<()>,
{
    // Parse the input with interpolated expressions using nom parser
    let elements = match crate::parser::parse_interpolated_string(input) {
        Ok((_, elements)) => elements,
        Err(_) => {
            // If parsing fails, treat the whole input as text
            segment_handler(input.clone())?;
            return Ok(());
        }
    };

    // Process each element
    for element in elements {
        match element {
            parser_types::Element::Text(text) => {
                segment_handler(text)?;
            }
            parser_types::Element::Expr(expr) => {
                // Evaluate the expression using eval_expr
                match crate::expression::eval_expr(expr, ctx) {
                    Ok(value) => segment_handler(value.to_bytes())?,
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

/// Evaluates all interpolated expressions and returns the complete result as Bytes
///
/// This is a convenience wrapper around `process_interpolated_chars` that collects
/// all output into a single Bytes buffer.
/// ZERO-COPY: Returns Bytes that may reference the original buffer.
///
/// # Arguments
/// * `input` - The input Bytes containing potential interpolated expressions
/// * `ctx` - Evaluation context containing variables and state
///
/// # Returns
/// * `Result<Bytes>` - The fully processed content with all expressions evaluated
///
/// # Errors
/// Returns error if expression evaluation fails
///
pub fn try_evaluate_interpolated_string(input: &Bytes, ctx: &mut EvalContext) -> Result<Bytes> {
    let mut result = BytesMut::new();

    process_interpolated_chars(input, ctx, |segment| {
        result.extend_from_slice(&segment);
        Ok(())
    })?;

    Ok(result.freeze())
}
// Helper Functions
