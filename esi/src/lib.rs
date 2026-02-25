#![doc = include_str!("../README.md")]

pub mod cache;
mod config;
mod error;
mod expression;
mod functions;
mod parser;
pub mod parser_types;

use crate::expression::EvalContext;
use crate::parser_types::Expr;
use bytes::{Buf, Bytes, BytesMut};
use fastly::http::request::{PendingRequest, PollResult};
use fastly::http::{header, Method, StatusCode, Url};
use fastly::{mime, Backend, Request, Response};
use log::debug;
use std::borrow::Cow;
use std::collections::VecDeque;
use std::io::{BufRead, Write};
use std::time::Duration;

pub use crate::error::{ExecutionError as ESIError, Result};
pub use crate::parser::{interpolated_content, parse, parse_complete, parse_expression};

pub use crate::config::Configuration;
pub use crate::error::ExecutionError;

type FragmentRequestDispatcher = dyn Fn(Request, Option<u32>) -> Result<PendingFragmentContent>;

type FragmentResponseProcessor = dyn Fn(&mut Request, Response) -> Result<Response>;

/// Representation of a fragment that is either being fetched, has already been fetched (or generated synthetically), or skipped.
pub enum PendingFragmentContent {
    PendingRequest(Box<PendingRequest>),
    CompletedRequest(Box<Response>),
    NoContent,
}

impl From<PendingRequest> for PendingFragmentContent {
    fn from(value: PendingRequest) -> Self {
        Self::PendingRequest(Box::new(value))
    }
}

impl From<Response> for PendingFragmentContent {
    fn from(value: Response) -> Self {
        Self::CompletedRequest(Box::new(value))
    }
}

/// Common metadata shared between main and alt fragment requests
#[derive(Clone)]
struct FragmentMetadata {
    /// Whether to continue on error
    continue_on_error: bool,
    /// Optional TTL override from the include tag (in seconds)
    ttl_override: Option<u32>,
    /// Optional timeout in milliseconds for this specific request
    maxwait: Option<u32>,
    // Request building parameters
    is_escaped: bool,
    /// Whether the request should be cached or not
    cacheable: bool,
    /// HTTP method to use for the request (default GET)
    method: Option<Bytes>,
    /// Optional body for POST requests
    entity: Option<Bytes>,
    /// Headers to append to the request
    appendheaders: Vec<(String, Bytes)>,
    /// Headers to remove from the request
    removeheaders: Vec<String>,
    /// Headers to set on the request
    setheaders: Vec<(String, Bytes)>,
}

/// Representation of an ESI fragment request with its metadata and pending response
pub struct Fragment {
    /// Metadata of the request
    pub(crate) req: Request,
    /// An optional alternate request to send if the original request fails
    pub(crate) alt_bytes: Option<Bytes>,
    /// The pending fragment response, which can be polled to retrieve the content
    pub(crate) pending_fragment: PendingFragmentContent,
    /// Common fragment metadata (shared with alt)
    pub(crate) metadata: FragmentMetadata,
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
    /// Returns the updated `PendingFragmentContent` (either still Pending or now Completed/NoContent)
    pub fn poll(self) -> Self {
        match self {
            Self::PendingRequest(pending_request) => match pending_request.poll() {
                PollResult::Done(result) => result.map_or_else(
                    |_| Self::NoContent,
                    |resp| Self::CompletedRequest(Box::new(resp)),
                ),
                PollResult::Pending(pending_request) => {
                    // Still pending - put it back
                    Self::PendingRequest(Box::new(pending_request))
                }
            },
            // Already completed - return as-is
            other => other,
        }
    }

    /// Check if the content is ready (completed or no content)
    pub const fn is_ready(&self) -> bool {
        !matches!(self, Self::PendingRequest(_))
    }

    /// Wait for and retrieve the response from a pending fragment request
    pub fn wait(self) -> Result<Response> {
        match self {
            Self::PendingRequest(pending_request) => pending_request.wait().map_err(|e| {
                ESIError::ExpressionError(format!("Fragment request wait failed: {e}"))
            }),
            Self::CompletedRequest(response) => Ok(*response),
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

    /// Get the evaluation context (for testing)
    ///
    /// Provides access to the processor's internal state including variables,
    /// response headers, status code, and body overrides set by ESI functions.
    pub const fn context(&self) -> &EvalContext {
        &self.ctx
    }

    /// Process a response body as an ESI document. Consumes the response body.
    ///
    /// This method processes ESI directives in the response body while streaming the output to the client,
    /// minimizing memory usage for large responses. It handles ESI includes, conditionals, and variable
    /// substitution according to the ESI specification.
    ///
    /// ## Response Manipulation Functions
    ///
    /// ESI functions can modify the response that gets sent to the client:
    ///
    /// ### `$add_header(name, value)`
    /// Adds a custom header to the response:
    /// ```text
    /// <esi:vars>$add_header('X-Custom-Header', 'my-value')</esi:vars>
    /// ```
    ///
    /// ### `$set_response_code(code [, body])`
    /// Sets the HTTP status code and optionally replaces the response body:
    /// ```text
    /// <esi:vars>$set_response_code(404, 'Page not found')</esi:vars>
    /// ```
    ///
    /// ### `$set_redirect(url [, code])`
    /// Sets up an HTTP redirect (default 302):
    /// ```text
    /// <esi:vars>$set_redirect('https://example.com/new-page')</esi:vars>
    /// <esi:vars>$set_redirect('https://example.com/moved', 301)</esi:vars>
    /// ```
    ///
    /// **Note:** These functions modify the response metadata that `process_response` will use
    /// when sending the response to the client. The headers, status code, and body override are
    /// buffered during processing and applied when the response is sent.
    ///
    /// # Arguments
    /// * `src_stream` - Source HTTP response containing ESI markup to process
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
    /// fn default_fragment_dispatcher(req: fastly::Request, maxwait: Option<u32>) -> esi::Result<esi::PendingFragmentContent> {
    ///     Ok(esi::PendingFragmentContent::CompletedRequest(
    ///         Box::new(fastly::Response::from_body("Fragment content"))
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
        mut self,
        src_stream: &mut Response,
        client_response_metadata: Option<Response>,
        dispatch_fragment_request: Option<&FragmentRequestDispatcher>,
        process_fragment_response: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        let mut output = Vec::new();

        self.process_stream(
            src_stream.take_body(),
            &mut output,
            dispatch_fragment_request,
            process_fragment_response,
        )?;

        let mut resp = client_response_metadata.unwrap_or_else(|| {
            Response::from_status(StatusCode::OK).with_content_type(mime::TEXT_HTML)
        });

        // Add Cache-Control header if configured to emit it
        if self.configuration.cache.rendered_cache_control {
            if let Some(cache_control_value) = self
                .ctx
                .cache_control_header(self.configuration.cache.rendered_ttl)
            {
                resp.set_header(header::CACHE_CONTROL, cache_control_value);
            }
        }

        for (name, value) in self.ctx.response_headers() {
            resp.set_header(name, value);
        }

        if let Some(status) = self.ctx.response_status() {
            let status_code = StatusCode::from_u16(status as u16).map_err(|_| {
                ExecutionError::FunctionError("set_response_code: invalid status code".to_string())
            })?;
            resp.set_status(status_code);
        }

        let body_bytes = self
            .ctx
            .response_body_override()
            .cloned()
            .unwrap_or_else(|| Bytes::from(output));

        resp.set_body(body_bytes.to_vec());
        resp.send_to_client();
        Ok(())
    }

    /// Process an ESI stream with industry-grade streaming architecture
    ///
    /// This is the low-level streaming API that processes ESI markup from any
    /// `BufRead` source to any `Write` destination. For processing Fastly responses,
    /// use [`process_response`](Self::process_response) instead.
    ///
    /// This method implements **three levels of streaming** for optimal performance:
    ///
    /// ## 1. Chunked Input Reading (Memory Efficient)
    /// - Reads source stream in 8KB chunks from `BufRead`
    /// - Accumulates chunks until parser can make progress
    /// - Prevents loading entire document into memory at once
    /// - Bounded memory growth with incremental processing
    ///
    /// ## 2. Streaming Output (Low Latency)
    /// - Writes processed content immediately as elements are parsed
    /// - Non-blocking poll checks for completed fragments
    /// - Output reaches destination with minimal delay
    /// - No buffering of final output
    ///
    /// ## 3. Streaming Fragments (Maximum Parallelism)
    /// - Dispatches all includes immediately (non-blocking)
    /// - Uses `select()` to process whichever fragment completes first
    /// - All fragments fetch in parallel, no wasted waiting
    /// - Try blocks dispatch all attempts' includes upfront
    ///
    /// ## Key Features:
    /// - Only fetches fragments that are actually needed (not those in unexecuted branches)
    /// - Fully recursive nested try/except blocks
    /// - Proper alt fallback and `continue_on_error` handling
    /// - Full ESI specification compliance
    ///
    /// ## Note on Parsing:
    /// The parser (nom-based) requires complete input for each parse operation.
    /// We handle this by buffering input chunks until a successful parse,
    /// then processing parsed elements immediately while retaining unparsed remainder.
    ///
    /// # Arguments
    /// * `src_stream` - BufRead source containing ESI markup (streams in chunks)
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
    pub fn process_stream(
        &mut self,
        mut src_stream: impl BufRead,
        output_writer: &mut impl Write,
        dispatch_fragment_request: Option<&FragmentRequestDispatcher>,
        process_fragment_response: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        // STREAMING INPUT PARSING:
        // Read chunks, parse incrementally, process elements as we parse them
        const CHUNK_SIZE: usize = 8192; // 8KB chunks
        const MAX_ITERATIONS: usize = 10000;

        // Set up fragment request dispatcher
        let dispatcher = dispatch_fragment_request.unwrap_or(&default_fragment_dispatcher);

        // Using BytesMut for zero-copy parsing
        let mut buffer = BytesMut::with_capacity(CHUNK_SIZE);
        let mut read_buf = vec![0u8; CHUNK_SIZE];
        let mut eof = false;
        let mut iterations = 0;

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
                match src_stream.read(&mut read_buf) {
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
                        let _ =
                            self.process_element_streaming(element, output_writer, dispatcher)?;
                        // Note: breaks at top-level are ignored
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
                        }
                        // Parsed everything in buffer, clear it and continue reading
                        buffer.clear();
                    } else {
                        // Have unparsed remainder
                        if eof {
                            // At EOF with unparsed data - already handled by parse_complete_bytes
                            // which treats remainder as Text elements
                            break;
                        }
                        // Keep remainder for next chunk - advance past consumed bytes
                        buffer.advance(consumed);
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
                Err(nom::Err::Error(e) | nom::Err::Failure(e)) => {
                    // Parse error
                    if eof {
                        // At EOF with parse error - this is a real error
                        return Err(ESIError::ExpressionError(format!("Parser error: {e:?}")));
                    }
                    // Not at EOF - maybe more data will help, output what we have and continue
                    output_writer.write_all(&buffer)?;
                    buffer.clear();
                }
            }
        }

        // DRAIN QUEUE: Wait for all remaining pending fragments (blocking waits)
        self.drain_queue(output_writer, dispatcher, process_fragment_response)?;

        Ok(())
    }

    /// Handle text or HTML content elements
    fn handle_content(&mut self, text: Bytes, output_writer: &mut impl Write) -> Result<bool> {
        if self.queue.is_empty() {
            // Not blocked - write immediately
            output_writer.write_all(&text)?;
        } else {
            // Blocked - queue it
            self.queue.push_back(QueuedElement::Content(text));
        }
        Ok(false)
    }

    /// Handle expression evaluation and output
    fn handle_expr(&mut self, expr: Expr, output_writer: &mut impl Write) -> Result<bool> {
        match expression::eval_expr(&expr, &mut self.ctx) {
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
        Ok(false)
    }

    /// Handle variable assignment
    fn handle_assign(&mut self, name: &str, subscript: Option<Expr>, value: &Expr) -> Result<bool> {
        let val = expression::eval_expr(value, &mut self.ctx)
            .unwrap_or(expression::Value::Text("".into()));

        if let Some(subscript_expr) = subscript {
            // Subscript assignment: modify existing collection
            if let Ok(subscript_val) = expression::eval_expr(&subscript_expr, &mut self.ctx) {
                let key_str = subscript_val.to_string();
                self.ctx.set_variable(name, Some(&key_str), val)?;
            }
        } else {
            // Regular assignment without subscript
            self.ctx.set_variable(name, None, val)?;
        }
        Ok(false)
    }

    /// Handle esi:vars tag (sets match name)
    fn handle_vars(&mut self, name: Option<String>) -> Result<bool> {
        if let Some(n) = name {
            self.ctx.set_match_name(&n);
        }
        Ok(false)
    }

    /// Handle esi:include tag
    fn handle_include(
        &mut self,
        params: &[(String, Expr)],
        attrs: &parser_types::IncludeAttributes,
        dispatcher: &FragmentRequestDispatcher,
    ) -> Result<bool> {
        let queued_element = self.process_include_tag(params, attrs, dispatcher)?;
        self.queue.push_back(queued_element);
        Ok(false)
    }

    /// Handle esi:choose tag
    fn handle_choose(
        &mut self,
        when_branches: Vec<parser_types::WhenBranch>,
        otherwise_events: Vec<parser_types::Element>,
        output_writer: &mut impl Write,
        dispatcher: &FragmentRequestDispatcher,
    ) -> Result<bool> {
        let mut chose_branch = false;

        for when_branch in when_branches {
            if let Some(ref match_name) = when_branch.match_name {
                self.ctx.set_match_name(match_name);
            }

            match expression::eval_expr(&when_branch.test, &mut self.ctx) {
                Ok(test_result) if test_result.to_bool() => {
                    // This branch matches - recursively process it
                    for elem in when_branch.content {
                        let break_encountered =
                            self.process_element_streaming(elem, output_writer, dispatcher)?;
                        if break_encountered {
                            return Ok(true); // Propagate break signal
                        }
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
                let break_encountered =
                    self.process_element_streaming(elem, output_writer, dispatcher)?;
                if break_encountered {
                    return Ok(true); // Propagate break signal
                }
            }
        }
        Ok(false)
    }

    /// Handle esi:try tag with attempts and except clause
    fn handle_try(
        &mut self,
        attempt_events: Vec<Vec<parser_types::Element>>,
        except_events: Vec<parser_types::Element>,
        output_writer: &mut impl Write,
        dispatcher: &FragmentRequestDispatcher,
    ) -> Result<bool> {
        let mut attempt_queues = Vec::new();

        for attempt in attempt_events {
            let attempt_queue = self.build_attempt_queue(attempt, output_writer, dispatcher)?;
            attempt_queues.push(attempt_queue);
        }

        // Process except clause elements
        let except_queue = self.build_attempt_queue(except_events, output_writer, dispatcher)?;

        // Add the try block to the queue with all attempts and except dispatched
        self.queue.push_back(QueuedElement::Try {
            attempt_elements: attempt_queues,
            except_elements: except_queue,
        });
        Ok(false)
    }

    /// Build a queue for attempt or except blocks
    fn build_attempt_queue(
        &mut self,
        elements: Vec<parser_types::Element>,
        output_writer: &mut impl Write,
        dispatcher: &FragmentRequestDispatcher,
    ) -> Result<Vec<QueuedElement>> {
        let mut queue = Vec::new();

        for elem in elements {
            match elem {
                parser_types::Element::Text(text) => {
                    queue.push(QueuedElement::Content(text));
                }
                parser_types::Element::Html(html) => {
                    queue.push(QueuedElement::Content(html));
                }
                parser_types::Element::Expr(expr) => {
                    match expression::eval_expr(&expr, &mut self.ctx) {
                        Ok(value) => {
                            if !matches!(value, expression::Value::Null) {
                                let bytes = value.to_bytes();
                                if !bytes.is_empty() {
                                    queue.push(QueuedElement::Content(bytes));
                                }
                            }
                        }
                        Err(e) => {
                            debug!("Expression evaluation failed: {e:?}");
                        }
                    }
                }
                parser_types::Element::Esi(parser_types::Tag::Include { params, attrs }) => {
                    // Dispatch the include and add to queue
                    let queued_element = self.process_include_tag(&params, &attrs, dispatcher)?;
                    queue.push(queued_element);
                }
                parser_types::Element::Esi(parser_types::Tag::Choose {
                    when_branches,
                    otherwise_events,
                }) => {
                    // Evaluate and process chosen branch inline
                    let mut chose_branch = false;
                    for when_branch in when_branches {
                        if let Some(match_name) = &when_branch.match_name {
                            self.ctx.set_match_name(match_name);
                        }
                        let test_result = expression::eval_expr(&when_branch.test, &mut self.ctx)?;
                        if test_result.to_bool() {
                            chose_branch = true;
                            for elem in when_branch.content {
                                self.process_element_streaming(elem, output_writer, dispatcher)?;
                                // Note: breaks within try blocks don't propagate out
                            }
                            break;
                        }
                    }
                    if !chose_branch {
                        for elem in otherwise_events {
                            self.process_element_streaming(elem, output_writer, dispatcher)?;
                            // Note: breaks within try blocks don't propagate out
                        }
                    }
                }
                parser_types::Element::Esi(parser_types::Tag::Try { .. }) => {
                    // Nested try blocks - process recursively
                    self.process_element_streaming(elem.clone(), output_writer, dispatcher)?;
                    // Note: breaks within try blocks don't propagate out
                }
                parser_types::Element::Esi(_) => {}
            }
        }

        Ok(queue)
    }

    /// Handle esi:foreach tag
    fn handle_foreach(
        &mut self,
        collection: Expr,
        item: Option<String>,
        content: &[parser_types::Element],
        output_writer: &mut impl Write,
        dispatcher: &FragmentRequestDispatcher,
    ) -> Result<bool> {
        // Evaluate the collection expression
        let collection_value =
            expression::eval_expr(&collection, &mut self.ctx).unwrap_or(expression::Value::Null);

        // Convert to a list if needed
        let items = match &collection_value {
            expression::Value::List(items) => items.clone(),
            expression::Value::Dict(map) => {
                // Convert dict entries to a list of 2-element lists [key, value]
                map.iter()
                    .map(|(k, v)| {
                        expression::Value::List(vec![
                            expression::Value::Text(k.clone().into()),
                            v.clone(),
                        ])
                    })
                    .collect()
            }
            expression::Value::Null => Vec::new(),
            other => vec![other.clone()], // Treat single values as a list of one
        };

        // Default item variable name if not specified
        let item_var = item.unwrap_or_else(|| "item".to_string());

        // Iterate through items
        'foreach_loop: for item_value in items {
            // Set the item variable
            self.ctx.set_variable(&item_var, None, item_value)?;

            // Process content for this iteration
            for elem in content {
                let break_encountered =
                    self.process_element_streaming(elem.clone(), output_writer, dispatcher)?;
                if break_encountered {
                    break 'foreach_loop;
                }
            }
        }
        Ok(false)
    }

    /// Process a single element in streaming mode
    fn process_element_streaming(
        &mut self,
        element: parser_types::Element,
        output_writer: &mut impl Write,
        dispatcher: &FragmentRequestDispatcher,
    ) -> Result<bool> {
        use parser_types::{Element, Tag};

        match element {
            Element::Text(text) | Element::Html(text) => self.handle_content(text, output_writer),

            Element::Expr(expr) => self.handle_expr(expr, output_writer),

            Element::Esi(Tag::Assign {
                name,
                subscript,
                value,
            }) => self.handle_assign(&name, subscript, &value),

            Element::Esi(Tag::Vars { name }) => self.handle_vars(name),

            Element::Esi(Tag::Include { params, attrs }) => {
                self.handle_include(&params, &attrs, dispatcher)
            }

            Element::Esi(Tag::Choose {
                when_branches,
                otherwise_events,
            }) => self.handle_choose(when_branches, otherwise_events, output_writer, dispatcher),

            Element::Esi(Tag::Try {
                attempt_events,
                except_events,
            }) => self.handle_try(attempt_events, except_events, output_writer, dispatcher),

            Element::Esi(Tag::Foreach {
                collection,
                item,
                content,
            }) => self.handle_foreach(collection, item, &content, output_writer, dispatcher),

            Element::Esi(Tag::Break) => Ok(true),

            Element::Esi(_) => Ok(false), // Other standalone tags shouldn't appear
        }
    }

    /// Evaluate an Expr to a Bytes value for use in includes
    /// Handles variable resolution, function calls, and string interpolation
    fn evaluate_expr_to_bytes(&mut self, expr: &Expr) -> Result<Bytes> {
        use crate::expression::eval_expr;

        // Evaluate the expression to get a Value
        let result = eval_expr(expr, &mut self.ctx)?;

        // Convert the Value to Bytes using the built-in to_bytes method
        Ok(result.to_bytes())
    }

    /// Helper to evaluate Include expressions and dispatch the request
    /// Returns a `QueuedElement` ready to be added to any queue (main/attempt/except)
    fn process_include_tag(
        &mut self,
        params: &[(String, Expr)],
        attrs: &parser_types::IncludeAttributes,
        dispatcher: &FragmentRequestDispatcher,
    ) -> Result<QueuedElement> {
        self.dispatch_include_to_element(params, attrs, dispatcher)
    }

    /// Dispatch an include and return a `QueuedElement` (for flexible queue insertion)
    /// This is the single source of truth for include dispatching logic
    fn dispatch_include_to_element(
        &mut self,
        params: &[(String, Expr)],
        attrs: &parser_types::IncludeAttributes,
        dispatcher: &FragmentRequestDispatcher,
    ) -> Result<QueuedElement> {
        // Evaluate src and alt expressions to get actual URLs
        let src_bytes = self.evaluate_expr_to_bytes(&attrs.src)?;
        let alt_bytes = attrs
            .alt
            .as_ref()
            .map(|e| self.evaluate_expr_to_bytes(e))
            .transpose()?;

        // Evaluate all metadata once (includes request params and TTL)
        let metadata = self.evaluate_request_params(attrs)?;

        // Evaluate params and append to URL
        // Use Cow to avoid allocation when params are empty and bytes are valid UTF-8
        let final_src = if params.is_empty() {
            src_bytes
        } else {
            let url_cow = String::from_utf8_lossy(&src_bytes);
            let mut url = String::with_capacity(url_cow.len() + params.len() * 20);
            url.push_str(&url_cow);

            let mut separator = if url.contains('?') { '&' } else { '?' };
            for (name, value_expr) in params {
                let value = self.evaluate_expr_to_bytes(value_expr)?;
                let value_str = String::from_utf8_lossy(&value);
                // Direct string building is more efficient than format!
                url.push(separator);
                url.push_str(name);
                url.push('=');
                url.push_str(&value_str);
                separator = '&';
            }
            Bytes::from(url)
        };

        let req = build_fragment_request(
            self.ctx.get_request().clone_without_body(),
            &final_src,
            &metadata,
        )?;

        let req_clone = req.clone_without_body();
        match dispatcher(req_clone, attrs.maxwait) {
            Ok(pending_fragment) => {
                let fragment = Fragment {
                    req,
                    alt_bytes,
                    pending_fragment,
                    metadata,
                };
                Ok(QueuedElement::Include(Box::new(fragment)))
            }
            Err(_) if attrs.continue_on_error => {
                // Try alt or add error placeholder
                if let Some(alt_src) = &alt_bytes {
                    let alt_req = build_fragment_request(
                        self.ctx.get_request().clone_without_body(),
                        alt_src,
                        &metadata,
                    )?;

                    let alt_req_without_body = alt_req.clone_without_body();
                    dispatcher(alt_req_without_body, attrs.maxwait).map_or_else(
                        |_| {
                            Ok(QueuedElement::Content(Bytes::from_static(
                                b"<!-- fragment request failed -->",
                            )))
                        },
                        //
                        |alt_pending| {
                            let fragment = Fragment {
                                req: alt_req,
                                alt_bytes: None,
                                pending_fragment: alt_pending,
                                metadata,
                            };
                            Ok(QueuedElement::Include(Box::new(fragment)))
                        },
                    )
                } else {
                    Ok(QueuedElement::Content(Bytes::from_static(
                        b"<!-- fragment request failed -->",
                    )))
                }
            }
            Err(e) => Err(ESIError::ExpressionError(format!(
                "Fragment dispatch failed: {e}"
            ))),
        }
    }

    /// Evaluate request parameters from `IncludeAttributes`
    fn evaluate_request_params(
        &mut self,
        attrs: &parser_types::IncludeAttributes,
    ) -> Result<FragmentMetadata> {
        // Parse TTL if provided (it's a literal string like "120m", not an expression)
        let ttl_override = attrs
            .ttl
            .as_ref()
            .and_then(|ttl_str| cache::parse_ttl(ttl_str));

        // Evaluate method if provided
        let method = attrs
            .method
            .as_ref()
            .map(|e| self.evaluate_expr_to_bytes(e))
            .transpose()?;

        // Evaluate entity if provided
        let entity = attrs
            .entity
            .as_ref()
            .map(|e| self.evaluate_expr_to_bytes(e))
            .transpose()?;

        // Evaluate header values
        let mut appendheaders = Vec::with_capacity(attrs.appendheaders.len());
        for (name, value_expr) in &attrs.appendheaders {
            let value_bytes = self.evaluate_expr_to_bytes(value_expr)?;
            appendheaders.push((name.clone(), value_bytes));
        }

        let mut setheaders = Vec::with_capacity(attrs.setheaders.len());
        for (name, value_expr) in &attrs.setheaders {
            let value_bytes = self.evaluate_expr_to_bytes(value_expr)?;
            setheaders.push((name.clone(), value_bytes));
        }

        // Determine if the fragment should be cached
        // cacheable=true means cache it, cacheable=false means bypass cache (set_pass)
        let cacheable = !attrs.no_store && self.configuration.cache.is_includes_cacheable;

        Ok(FragmentMetadata {
            continue_on_error: attrs.continue_on_error,
            ttl_override,
            maxwait: attrs.maxwait,
            is_escaped: self.configuration.is_escaped_content,
            cacheable,
            method,
            entity,
            appendheaders,
            removeheaders: attrs.removeheaders.clone(),
            setheaders,
        })
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
                        &mut fragment.pending_fragment,
                        PendingFragmentContent::NoContent,
                    );
                    fragment.pending_fragment = pending_content.poll();

                    // Check if it's ready now
                    if fragment.pending_fragment.is_ready() {
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

    /// Drain queue with efficient waiting using `select()`
    /// Uses `select()` to process whichever pending request completes first
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
                            fragment.pending_fragment,
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
                    &mut fragment.pending_fragment,
                    PendingFragmentContent::NoContent,
                ) {
                    pending_reqs.push(*pending_req);
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

            // Update the completed fragment with the result and track TTL if rendered caching enabled
            completed_fragment.pending_fragment = result.map_or_else(
                |_| PendingFragmentContent::NoContent,
                |resp| {
                    // Track TTL if we need it for rendered document (for tracking OR header emission)
                    if self.configuration.cache.is_rendered_cacheable
                        || self.configuration.cache.rendered_cache_control
                    {
                        // Use ttl_override from the include tag if present, otherwise calculate from response
                        let ttl = if let Some(override_ttl) =
                            completed_fragment.metadata.ttl_override
                        {
                            debug!("Using TTL override from include tag: {override_ttl} seconds");
                            Some(override_ttl)
                        } else {
                            match cache::calculate_ttl(&resp, &self.configuration.cache) {
                                Ok(Some(ttl)) => {
                                    debug!("Calculated TTL from response: {ttl} seconds");
                                    Some(ttl)
                                }
                                Ok(None) => {
                                    debug!("Response not cacheable");
                                    None
                                }
                                Err(e) => {
                                    debug!("Error calculating TTL: {e:?}");
                                    None
                                }
                            }
                        };

                        if let Some(ttl_value) = ttl {
                            self.ctx.update_cache_min_ttl(ttl_value);
                            debug!("Tracking TTL {ttl_value} for rendered document");
                        }
                    }
                    PendingFragmentContent::CompletedRequest(Box::new(resp))
                },
            );

            // Put remaining fragments back in queue (with their pending requests restored)
            for (pending_req, (_idx, mut fragment)) in
                remaining.into_iter().zip(fragments_by_request)
            {
                fragment.pending_fragment =
                    PendingFragmentContent::PendingRequest(Box::new(pending_req));
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
        &self,
        fragment: Fragment,
        output_writer: &mut impl Write,
        dispatcher: &FragmentRequestDispatcher,
        processor: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        let continue_on_error = fragment.metadata.continue_on_error;

        // Wait for response
        let response = fragment.pending_fragment.wait()?;

        // Apply processor if provided
        let mut req_for_processor = fragment.req.clone_without_body();
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
        } else if let Some(alt_src) = fragment.alt_bytes {
            // Try alt - reuse metadata from original request
            debug!("Main request failed, trying alt");
            let alt_req = build_fragment_request(
                self.ctx.get_request().clone_without_body(),
                &alt_src,
                &fragment.metadata,
            )?;

            let alt_req_without_body = alt_req.clone_without_body();
            match dispatcher(alt_req_without_body, fragment.metadata.maxwait) {
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
// Uses dynamic backends to support maxwait attribute as first_byte_timeout
fn default_fragment_dispatcher(
    req: Request,
    maxwait: Option<u32>,
) -> Result<PendingFragmentContent> {
    debug!("no dispatch method configured, defaulting to hostname");
    let host = req
        .get_url()
        .host()
        .unwrap_or_else(|| panic!("no host in request: {}", req.get_url()))
        .to_string();

    // Build a dynamic backend with appropriate settings
    let mut builder = Backend::builder(&host, &host)
        .override_host(&host)
        .enable_ssl()
        .sni_hostname(&host);

    // Add timeout if `maxwait` is specified
    if let Some(timeout_ms) = maxwait {
        builder = builder.first_byte_timeout(Duration::from_millis(u64::from(timeout_ms)));
    }

    let backend = builder
        .finish()
        .map_err(|e| ExecutionError::ExpressionError(format!("Failed to create backend: {e}")))?;

    let pending_req = req.send_async(backend)?;
    Ok(PendingFragmentContent::PendingRequest(Box::new(
        pending_req,
    )))
}

// Helper function to build a fragment request from a URL
// For HTML content the URL is unescaped if it's escaped (default).
// It can be disabled in the processor configuration for a non-HTML content.
fn build_fragment_request(
    mut request: Request,
    url: &Bytes,
    metadata: &FragmentMetadata,
) -> Result<Request> {
    // Convert Bytes to str for URL parsing
    let url_str = std::str::from_utf8(url)
        .map_err(|_| ExecutionError::ExpressionError("Invalid UTF-8 in URL".to_string()))?;

    let escaped_url = if metadata.is_escaped {
        Cow::Owned(html_escape::decode_html_entities(url_str).into_owned())
    } else {
        Cow::Borrowed(url_str)
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
                return Err(ExecutionError::InvalidRequestUrl(escaped_url.into_owned()));
            }
        }
    } else {
        request.set_url(match Url::parse(&escaped_url) {
            Ok(url) => url,
            Err(_err) => {
                return Err(ExecutionError::InvalidRequestUrl(escaped_url.into_owned()));
            }
        });
    }

    let hostname = request.get_url().host().expect("no host").to_string();

    request.set_header(header::HOST, &hostname);

    // Set HTTP method (default is GET)
    if let Some(method_bytes) = &metadata.method {
        let method_str = std::str::from_utf8(method_bytes)
            .map_err(|_| ExecutionError::ExpressionError("Invalid UTF-8 in method".to_string()))?
            .to_uppercase();

        match method_str.as_str() {
            "GET" => request.set_method(Method::GET),
            "POST" => request.set_method(Method::POST),
            _ => {
                return Err(ExecutionError::ExpressionError(format!(
                    "Unsupported HTTP method: {method_str}"
                )))
            }
        }
    }

    // Set POST body if provided
    if let Some(entity_bytes) = &metadata.entity {
        if request.get_method() == Method::POST {
            request.set_body(entity_bytes.as_ref());
        }
    }

    // Process header manipulations in the correct order:
    // 1. Remove headers
    for header_name in &metadata.removeheaders {
        request.remove_header(header_name);
    }

    // 2. Set headers (replace existing)
    for (name, value) in &metadata.setheaders {
        request.set_header(name, value.as_ref());
    }

    // 3. Append headers (add to existing)
    for (name, value) in &metadata.appendheaders {
        request.append_header(name, value.as_ref());
    }

    // Set pass option to bypass cache if fragment is not cacheable
    if !metadata.cacheable {
        request.set_pass(true);
    }

    Ok(request)
}

// Helper Functions
