#![doc = include_str!("../README.md")]

pub(crate) mod cache;
mod config;
mod element_handler;
mod error;
mod expression;
mod functions;
mod literals;
mod parser;
pub(crate) mod parser_types;

use crate::element_handler::{ElementHandler, Flow};
use crate::expression::EvalContext;
use crate::parser_types::{DcaMode, IncludeAttributes};
#[cfg(not(feature = "expose-internals"))]
use crate::parser_types::{Element, Expr};
use bytes::{Bytes, BytesMut};
use fastly::http::request::{select, PendingRequest};
use fastly::http::{header, Method, StatusCode, Url};
use fastly::{mime, Backend, Request, Response};
use log::debug;
use std::borrow::Cow;
use std::collections::{HashMap, VecDeque};
use std::io::{BufRead, Write};
use std::time::Duration;

pub use crate::error::{ESIError, Result};
#[cfg(feature = "expose-internals")]
pub use crate::parser::parse;
#[cfg(feature = "expose-internals")]
pub use crate::parser::{interpolated_content, parse_expression, parse_remainder};

pub use crate::cache::CacheConfig;
pub use crate::config::Configuration;
#[cfg(feature = "expose-internals")]
pub use crate::parser_types::{Element, Expr, Tag};

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

/// Evaluated fragment request metadata
/// Store evaluated values once to avoid re-evaluation on alt fallback
struct FragmentMetadata {
    /// HTTP method to use for the request (default GET)
    method: Option<Bytes>,
    /// Optional body for POST requests
    entity: Option<Bytes>,
    /// Headers to set on the request
    setheaders: Vec<(String, Bytes)>,
    /// Headers to append to the request
    appendheaders: Vec<(String, Bytes)>,
    /// Headers to remove from the request
    removeheaders: Vec<String>,
    /// Whether the request should be cached or not
    cacheable: bool,
    /// Optional TTL override from the include tag (in seconds)
    ttl_override: Option<u32>,
    // Flags needed for fragment processing
    continue_on_error: bool,
    /// Optional timeout in milliseconds for this specific request
    maxwait: Option<u32>,
    /// Dynamic Content Assembly mode for this request I(controls pre-processing)
    dca: DcaMode,
}

/// Representation of an ESI fragment request with its metadata and pending response
pub struct Fragment {
    /// Metadata of the request
    pub(crate) req: Request,
    /// An optional alternate request to send if the original request fails
    pub(crate) alt_bytes: Option<Bytes>,
    /// The pending fragment response, which can be polled to retrieve the content
    pub(crate) pending_fragment: PendingFragmentContent,
    /// Evaluated parameters (reusable for alt fallback)
    pub(crate) metadata: FragmentMetadata,
}

/// Queue element for streaming processing
/// Elements that need to be executed in order
enum QueuedElement {
    /// Raw content ready to write (text/html/evaluated expressions)
    Content(Bytes),
    /// A dispatched include waiting to be executed
    Include(Box<Fragment>),
    /// A try block with unevaluated attempt/except elements.
    /// Elements are executed lazily in document order when the block is drained.
    Try {
        attempt_elements: Vec<Vec<Element>>,
        except_elements: Vec<Element>,
    },
}

// ---------------------------------------------------------------------------
// Parallel try-block tracking types (flat-buf design)
// ---------------------------------------------------------------------------

#[derive(Hash, Eq, PartialEq, Clone)]
struct RequestKey {
    method: Method,
    url: String,
}

/// Tracks an in-flight `<esi:try>` block in `drain_queue`.
///
/// Try-block includes share the main `buf` slots (same as bare includes)
/// instead of maintaining a separate `content_slots` system.  Each attempt
/// records which `buf` indices hold its content so that assembly can
/// concatenate them once every pending include has been resolved.
struct TryBlockTracker {
    /// `buf` slot reserved for the assembled try-block output.
    outer_slot: usize,
    /// Per-attempt tracking (document order).
    attempts: Vec<AttemptTracker>,
    /// Deferred until all attempts resolve; only evaluated if any attempt
    /// failed.
    except_elements: Vec<Element>,
    /// Total in-flight includes across all attempts.  When this reaches
    /// zero the block is ready to assemble.
    pending_count: usize,
}

/// Per-attempt state inside a [`TryBlockTracker`].
struct AttemptTracker {
    /// Indices into the main `buf` vec that hold this attempt's content
    /// (both static text and resolved includes), in document order.
    buf_slots: Vec<usize>,
    /// Set to `true` if any include in this attempt returned a non-success
    /// status without `continue_on_error`.
    failed: bool,
}

/// Entry in the `url_map` that correlates a completing `PendingRequest`
/// back to the `buf` slot it should fill.
///
/// A single struct covers both bare `<esi:include>`s and includes inside
/// `<esi:try>` blocks — the `try_info` field distinguishes the two cases.
struct SlotEntry {
    /// Index into the main `buf` vec to fill with the processed response.
    buf_slot: usize,
    /// Fragment metadata needed to process the response (alt, headers, dca…).
    fragment: Box<Fragment>,
    /// `Some((tracker_idx, attempt_idx))` when this include lives inside a
    /// try block; `None` for a bare include.
    try_info: Option<(usize, usize)>,
}

impl PendingFragmentContent {
    /// Check if the content is ready (completed or no content)
    pub const fn is_ready(&self) -> bool {
        !matches!(self, Self::PendingRequest(_))
    }

    /// Wait for and retrieve the response from a pending fragment request
    pub fn wait(self) -> Result<Response> {
        match self {
            Self::PendingRequest(pending_request) => pending_request.wait().map_err(|e| {
                ESIError::FragmentRequestError(format!("fragment request wait failed: {e}"))
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

/// [`ElementHandler`] implementation for top-level ESI document processing.
///
/// Pairs with [`FunctionHandler`](crate::expression::FunctionHandler) — together they are the two
/// concrete implementors of the trait, distinguished by execution context: this one drives
/// [`Processor`]'s streaming pipeline, giving the shared default methods access to the
/// output writer, the fragment dispatcher, and the ready-queue.
//
// (contrast with `FunctionHandler` in expression.rs, which drives user-defined function bodies)
struct DocumentHandler<'a, W: Write> {
    processor: &'a mut Processor,
    output: &'a mut W,
    dispatch_fragment_request: &'a FragmentRequestDispatcher,
    fragment_response_handler: Option<&'a FragmentResponseProcessor>,
}

impl<W: Write> ElementHandler for DocumentHandler<'_, W> {
    fn ctx(&mut self) -> &mut EvalContext {
        &mut self.processor.ctx
    }

    fn process_queue(&mut self) -> crate::Result<()> {
        self.processor.process_queue(
            self.output,
            self.dispatch_fragment_request,
            self.fragment_response_handler,
        )
    }

    fn write_bytes(&mut self, bytes: Bytes) -> crate::Result<()> {
        if self.processor.queue.is_empty() {
            // Not blocked - write immediately
            self.output
                .write_all(&bytes)
                .map_err(ESIError::WriterError)?;
        } else {
            // Blocked by a pending fragment - enqueue for later
            self.processor
                .queue
                .push_back(QueuedElement::Content(bytes));
        }
        Ok(())
    }

    fn on_return(&mut self, _value: &Expr) -> crate::Result<Flow> {
        // Return tags should only appear inside function bodies, not at the streaming level
        Ok(Flow::Continue)
    }

    fn on_include(&mut self, attrs: &IncludeAttributes) -> crate::Result<Flow> {
        let queued_element = self
            .processor
            .dispatch_include(attrs, self.dispatch_fragment_request)?;
        self.processor.queue.push_back(queued_element);
        Ok(Flow::Continue)
    }

    /// Handle `<esi:eval …/>` — BLOCKING operation that fetches and re-processes content as ESI.
    ///
    /// The `dca` attribute controls processing mode:
    /// - `dca="none"` (default): fragment executed in parent's context (shared variables).
    /// - `dca="esi"`:  fragment executed in an isolated context (output only, no variable leakage).
    fn on_eval(&mut self, attrs: &IncludeAttributes) -> crate::Result<Flow> {
        // Build and dispatch the request (same machinery as include, but blocking)
        let queued_element = self
            .processor
            .dispatch_include(attrs, self.dispatch_fragment_request)?;

        match queued_element {
            QueuedElement::Include(fragment) => {
                // Eval is BLOCKING - wait for the response immediately
                let response = fragment.pending_fragment.wait()?;

                if !response.get_status().is_success() {
                    if fragment.metadata.continue_on_error {
                        // Per ESI spec: onerror="continue" deletes the tag with no output
                        return Ok(Flow::Continue);
                    }
                    return Err(ESIError::UnexpectedStatus {
                        url: "eval".to_string(),
                        status: response.get_status().as_u16(),
                    });
                }

                // Get the response body
                let body_bytes = response.into_body_bytes();
                let body_as_bytes = Bytes::from(body_bytes);

                // ALWAYS parse as ESI (this is the key difference from include)
                let (rest, elements) = parser::parse_remainder(&body_as_bytes).map_err(|e| {
                    ESIError::ParseError(format!("failed to parse eval fragment: {e}"))
                })?;

                if !rest.is_empty() {
                    return Err(ESIError::ParseError(
                        "incomplete parse of eval fragment".into(),
                    ));
                }

                if fragment.metadata.dca == DcaMode::Esi {
                    // dca="esi": TWO-PHASE processing
                    // Phase 1: Process fragment in ISOLATED context
                    // Reborrow before the exclusive borrow of self.processor below
                    let dispatcher = self.dispatch_fragment_request;
                    let resp_handler = self.fragment_response_handler;
                    let mut isolated_processor = Processor::new(
                        Some(self.processor.ctx.get_request().clone_without_body()),
                        self.processor.configuration.clone(),
                    );
                    let mut isolated_output = Vec::new();

                    {
                        let mut isolated_handler = DocumentHandler {
                            processor: &mut isolated_processor,
                            output: &mut isolated_output,
                            dispatch_fragment_request: dispatcher,
                            fragment_response_handler: resp_handler,
                        };
                        for element in elements {
                            isolated_handler.process(&element)?;
                        }
                        // isolated_handler drops here, releasing the mutable borrow of isolated_output
                    }

                    // Drain any includes dispatched during Phase 1 (e.g. <esi:include> inside the eval'd fragment).
                    // Must happen before we read isolated_output, while isolated_handler has already dropped.
                    isolated_processor.drain_queue(
                        &mut isolated_output,
                        dispatcher,
                        resp_handler,
                    )?;

                    // Phase 2: Parse the isolated output as ESI and process in PARENT's context
                    // This is why variables don't leak: they only exist in phase 1
                    let isolated_bytes = Bytes::from(isolated_output);
                    let (rest, output_elements) = parser::parse_remainder(&isolated_bytes)
                        .map_err(|e| {
                            ESIError::ParseError(format!(
                                "failed to parse eval isolated output: {e}",
                            ))
                        })?;

                    if !rest.is_empty() {
                        return Err(ESIError::ParseError(
                            "incomplete parse of eval isolated output".into(),
                        ));
                    }

                    for element in output_elements {
                        if matches!(self.process(&element)?, Flow::Break) {
                            return Ok(Flow::Break);
                        }
                    }
                } else {
                    // dca="none": SINGLE-PHASE processing in PARENT's context
                    // Fragment included first, then executed in parent (variables affect parent)
                    for element in elements {
                        if matches!(self.process(&element)?, Flow::Break) {
                            return Ok(Flow::Break); // Propagate break from eval'd content
                        }
                    }
                }

                Ok(Flow::Continue)
            }
            QueuedElement::Content(_) => {
                // Error with continue_on_error - insert nothing per spec
                Ok(Flow::Continue)
            }
            _ => unreachable!("dispatch_include_to_element should only return Include or Content"),
        }
    }

    fn on_try(
        &mut self,
        attempt_events: Vec<Vec<Element>>,
        except_events: Vec<Element>,
    ) -> crate::Result<Flow> {
        // Store raw elements; they will be evaluated lazily in document order
        // when the try block is drained.  This ensures variable assignments
        // made by earlier elements in the attempt are visible to later includes.
        self.processor.queue.push_back(QueuedElement::Try {
            attempt_elements: attempt_events,
            except_elements: except_events,
        });
        Ok(Flow::Continue)
    }

    fn on_function(&mut self, name: String, body: Vec<Element>) -> crate::Result<Flow> {
        // Register user-defined function in the evaluation context
        self.processor.ctx.register_function(name, body);
        Ok(Flow::Continue)
    }
}

/// Implementation of the main Processor methods driving ESI processing
///
/// This impl block contains the core logic for processing ESI documents, including
/// the main streaming loop, fragment dispatching, and queue management. The
/// DocumentHandler implementation above delegates to these methods for the actual processing work,
/// allowing the handler to focus on interfacing with the streaming architecture and the evaluation context.
impl Processor {
    pub fn new(original_request_metadata: Option<Request>, configuration: Configuration) -> Self {
        let mut ctx = EvalContext::new();
        if let Some(req) = original_request_metadata {
            ctx.set_request(req);
        } else {
            ctx.set_request(Request::new(Method::GET, "http://localhost"));
        }
        // Apply configuration settings to context
        ctx.set_max_function_recursion_depth(configuration.function_recursion_depth);
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

    /// Return the error for failed fragment requests.
    ///
    /// For HTML content (`is_escaped_content = true`) an HTML comment is inserted
    /// so that the failure is visible in the rendered document.  For non-HTML
    /// content (JSON, XML, …) nothing is emitted to avoid polluting the output
    /// with HTML comment syntax.
    const fn fragment_req_failed(&self) -> &'static [u8] {
        if self.configuration.is_escaped_content {
            FRAGMENT_REQUEST_FAILED
        } else {
            b""
        }
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
    /// # Ok::<(), esi::ESIError>(())
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

        // Apply any response headers set during processing
        for (name, value) in self.ctx.response_headers() {
            resp.set_header(name, value);
        }

        if let Some(status) = self.ctx.response_status() {
            let status_code = StatusCode::from_u16(status as u16).map_err(|_| {
                ESIError::FunctionError("set_response_code: invalid status code".to_string())
            })?;
            resp.set_status(status_code);
        }

        let body_bytes = self
            .ctx
            .response_body_override()
            .cloned()
            .unwrap_or_else(|| Bytes::from(output));

        resp.set_body(body_bytes.as_ref());
        resp.send_to_client();
        Ok(())
    }

    /// Process an ESI stream from any `BufRead` into a `Write`.
    ///
    /// - Reads in configurable-size chunks (default 16 KB), buffering only what the parser needs
    /// - Parses incrementally; writes content as soon as it’s parsed
    /// - Dispatches includes immediately; waits for them later in document order
    /// - Uses `select()` to harvest in-flight includes while preserving output order
    ///
    /// For Fastly `Response` bodies, prefer `process_response`, which wires up
    /// cache headers and response metadata for you.
    ///
    /// # Arguments
    /// * `src_stream` - `BufRead` source containing ESI markup (streams in chunks)
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
        let chunk_size = self.configuration.chunk_size;
        const MAX_ITERATIONS: usize = 10000;

        // Set up fragment request dispatcher
        let dispatcher = dispatch_fragment_request.unwrap_or(&default_fragment_dispatcher);

        // Using BytesMut for zero-copy parsing
        let mut buffer = BytesMut::with_capacity(chunk_size);
        let mut read_buf = vec![0u8; chunk_size];
        let mut eof = false;
        let mut iterations = 0;

        loop {
            iterations += 1;
            if iterations > MAX_ITERATIONS {
                return Err(ESIError::InfiniteLoop {
                    iterations,
                    buffer_len: buffer.len(),
                    eof,
                });
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

            // Create a zero-copy window of the current buffer contents without cloning.
            // split_off(0) moves the data into a new view while keeping the same backing store.
            let mut window = buffer.split_off(0);
            let frozen = window.freeze();

            // Try to parse what we have in the buffer
            // Use streaming parser unless we're at EOF, then use complete parser
            let parse_result = if eof {
                // At EOF - use complete parser which handles Incomplete by treating remainder as text
                parser::parse_remainder(&frozen)
            } else {
                // Still streaming - use streaming parser
                parser::parse(&frozen)
            };

            match parse_result {
                Ok((remaining, elements)) => {
                    // Successfully parsed some elements
                    let mut handler = DocumentHandler {
                        processor: self,
                        output: output_writer,
                        dispatch_fragment_request: dispatcher,
                        fragment_response_handler: process_fragment_response,
                    };
                    for element in elements {
                        // Note: breaks at top-level are ignored
                        handler.process(&element)?;
                        // After each element, check if any queued includes are ready
                        handler.process_queue()?;
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
                        // Reuse the existing backing store without cloning: split_off leaves
                        // `window` empty; reuse it for the remainder so we avoid copying.
                        let remainder_bytes = frozen.slice(consumed..);
                        window = BytesMut::from(remainder_bytes.as_ref());
                        buffer = window.split_off(0);
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
                        return Err(ESIError::ParseError(format!("parser error: {e:?}")));
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

    /// Evaluate request parameters from `IncludeAttributes` and return a `FragmentMetadata` struct
    ///
    /// Evaluate original tag attributes and compute all values needed for dispatching a fragment request
    fn evaluate_request_params(&mut self, attrs: &IncludeAttributes) -> Result<FragmentMetadata> {
        // Parse TTL if provided (it's a literal string like "120m", not an expression)
        let ttl_override = attrs
            .ttl
            .as_ref()
            .and_then(|ttl_str| cache::parse_ttl(ttl_str));

        // Evaluate method if provided
        let method = attrs
            .method
            .as_ref()
            .map(|e| eval_expr_to_bytes(e, &mut self.ctx))
            .transpose()?;

        // Evaluate entity if provided
        let entity = attrs
            .entity
            .as_ref()
            .map(|e| eval_expr_to_bytes(e, &mut self.ctx))
            .transpose()?;

        // Evaluate header values
        let mut setheaders = Vec::with_capacity(attrs.setheaders.len());
        for (name, value_expr) in &attrs.setheaders {
            let value_bytes = eval_expr_to_bytes(value_expr, &mut self.ctx)?;
            setheaders.push((name.clone(), value_bytes));
        }

        let mut appendheaders = Vec::with_capacity(attrs.appendheaders.len());
        for (name, value_expr) in &attrs.appendheaders {
            let value_bytes = eval_expr_to_bytes(value_expr, &mut self.ctx)?;
            appendheaders.push((name.clone(), value_bytes));
        }

        // Determine if the fragment should be cached
        let cacheable = !attrs.no_store && self.configuration.cache.is_includes_cacheable;

        Ok(FragmentMetadata {
            method,
            entity,
            setheaders,
            appendheaders,
            removeheaders: attrs.removeheaders.clone(),
            cacheable,
            ttl_override,
            continue_on_error: attrs.continue_on_error,
            maxwait: attrs.maxwait,
            dca: attrs.dca,
        })
    }

    /// Dispatch an include and return a `QueuedElement` (for flexible queue insertion)
    /// This is the single source of truth for include dispatching logic
    fn dispatch_include(
        &mut self,
        attrs: &IncludeAttributes,
        dispatcher: &FragmentRequestDispatcher,
    ) -> Result<QueuedElement> {
        // Evaluate src and alt expressions to get actual URLs
        let src_bytes = eval_expr_to_bytes(&attrs.src, &mut self.ctx)?;
        let alt_bytes = attrs
            .alt
            .as_ref()
            .map(|e| eval_expr_to_bytes(e, &mut self.ctx))
            .transpose()?;

        // Evaluate all metadata once (includes request params and TTL)
        let metadata = self.evaluate_request_params(attrs)?;

        // Evaluate params and append to URL
        // Use Cow to avoid allocation when params are empty and bytes are valid UTF-8
        let final_src = if attrs.params.is_empty() {
            src_bytes
        } else {
            let url_cow = String::from_utf8_lossy(&src_bytes);
            let mut url = String::with_capacity(url_cow.len() + attrs.params.len() * 20);
            url.push_str(&url_cow);

            let mut separator = if url.contains('?') { '&' } else { '?' };
            for (name, value_expr) in &attrs.params {
                let value = eval_expr_to_bytes(value_expr, &mut self.ctx)?;
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
            &self.configuration,
        )?;

        let req_clone = req.clone_without_body();
        match dispatcher(req_clone, metadata.maxwait) {
            Ok(pending_fragment) => {
                let fragment = Fragment {
                    req,
                    alt_bytes,
                    pending_fragment,
                    metadata,
                };
                Ok(QueuedElement::Include(Box::new(fragment)))
            }
            Err(_) if metadata.continue_on_error => {
                // Try alt or add error placeholder
                if let Some(alt_src) = &alt_bytes {
                    let alt_req = build_fragment_request(
                        self.ctx.get_request().clone_without_body(),
                        alt_src,
                        &metadata,
                        &self.configuration,
                    )?;

                    let alt_req_without_body = alt_req.clone_without_body();
                    dispatcher(alt_req_without_body, metadata.maxwait).map_or_else(
                        |_| {
                            Ok(QueuedElement::Content(Bytes::from_static(
                                self.fragment_req_failed(),
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
                        self.fragment_req_failed(),
                    )))
                }
            }
            Err(e) => Err(ESIError::FragmentRequestError(format!(
                "fragment dispatch failed: {e}"
            ))),
        }
    }

    /// Check ready queue items — non-blocking poll.
    ///
    /// Processes completed fragments, ready content, and try blocks from the front of the
    /// queue without blocking. Stops as soon as it encounters a pending include.
    fn process_queue(
        &mut self,
        output_writer: &mut impl Write,
        dispatcher: &FragmentRequestDispatcher,
        processor: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        loop {
            match self.queue.pop_front() {
                None => break,
                Some(QueuedElement::Content(content)) => {
                    // Content is always ready - write immediately
                    output_writer.write_all(&content)?;
                }
                Some(QueuedElement::Include(mut fragment)) => {
                    // If the fragment is already completed (cache hit / NoContent),
                    // process immediately. Otherwise, leave it in place and exit
                    // to avoid busy-wait polling.
                    let pending_content = std::mem::replace(
                        &mut fragment.pending_fragment,
                        PendingFragmentContent::NoContent,
                    );
                    match pending_content {
                        PendingFragmentContent::PendingRequest(request) => {
                            fragment.pending_fragment =
                                PendingFragmentContent::PendingRequest(request);
                            self.queue.push_front(QueuedElement::Include(fragment));
                            break;
                        }
                        ready => {
                            fragment.pending_fragment = ready;
                            self.process_include(*fragment, output_writer, dispatcher, processor)?;
                        }
                    }
                }
                Some(QueuedElement::Try {
                    attempt_elements,
                    except_elements,
                }) => {
                    // Process try blocks inline rather than stalling the queue.
                    // Previously Try was skipped here, causing a stall whenever a Try block
                    // reached the front after a preceding include was consumed.
                    self.process_try_block(
                        attempt_elements,
                        &except_elements,
                        output_writer,
                        dispatcher,
                        processor,
                    )?;
                }
            }
        }
        Ok(())
    }

    /// Build a correlation key for matching select() results to dispatched requests.
    fn make_request_key(req: &Request) -> RequestKey {
        RequestKey {
            method: req.get_method().clone(),
            url: req.get_url_str().to_string(),
        }
    }

    /// Drain the queue to completion, preserving document order while using
    /// `fastly::http::request::select()` to process whichever in-flight include
    /// finishes first.
    ///
    /// - All includes (bare and inside `<esi:try>`) are dispatched before any
    ///   waits; a single pending pool feeds `select()`, removing the xN
    ///   sequential penalty for many consecutive try blocks.
    /// - Each queued element gets a slot in `buf`; try-block includes use the
    ///   same `buf` slots as bare includes (no separate content_slots system).
    ///   A `TryBlockTracker` records which buf indices belong to each attempt
    ///   so they can be assembled into the outer slot when resolved.
    /// - Request correlation uses (method + URL) keys via `SlotEntry`; the
    ///   `try_info` field distinguishes bare includes from try-block includes.
    fn drain_queue(
        &mut self,
        output_writer: &mut impl Write,
        dispatch_fragment_request: &FragmentRequestDispatcher,
        process_fragment_response: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        // `buf[i]` is `None` while the slot is waiting for a response,
        // `Some(bytes)` once it is ready.  Try-block includes use the SAME
        // buf slots as bare includes — no separate content_slots system.
        let mut buf: Vec<Option<Bytes>> = Vec::with_capacity(self.queue.len());
        let mut next_out: usize = 0;

        // RequestKey -> FIFO queue of SlotEntry for all in-flight requests.
        // A single SlotEntry struct covers both bare includes and try-block
        // includes; the `try_info` field distinguishes the two cases.
        let mut url_map: HashMap<RequestKey, VecDeque<SlotEntry>> = HashMap::new();

        // PendingRequests handed to select() on each iteration.
        let mut pending: Vec<PendingRequest> = Vec::new();

        // One tracker per <esi:try> block encountered during Step 1.
        let mut try_trackers: Vec<TryBlockTracker> = Vec::new();

        loop {
            // ------------------------------------------------------------------
            // Step 1: drain self.queue, assigning every element a slot.
            //
            // After this inner loop self.queue is guaranteed empty.  That
            // invariant means DocumentHandler::write_bytes() called from within
            // `process_include` writes directly to the caller-supplied
            // slot_buf rather than re-queuing (the correct behaviour for
            // dca="esi" fragment bodies that contain further ESI directives).
            // ------------------------------------------------------------------
            while let Some(elem) = self.queue.pop_front() {
                match elem {
                    QueuedElement::Content(bytes) => {
                        buf.push(Some(bytes));
                    }

                    QueuedElement::Include(mut fragment) => {
                        let slot = buf.len();
                        buf.push(None); // placeholder; filled when response arrives

                        let pending_content = std::mem::replace(
                            &mut fragment.pending_fragment,
                            PendingFragmentContent::NoContent,
                        );
                        match pending_content {
                            PendingFragmentContent::PendingRequest(req) => {
                                let key = Self::make_request_key(&fragment.req);
                                url_map.entry(key).or_default().push_back(SlotEntry {
                                    buf_slot: slot,
                                    fragment,
                                    try_info: None,
                                });
                                pending.push(*req);
                            }
                            ready => {
                                // CompletedRequest or NoContent: process now.
                                fragment.pending_fragment = ready;
                                let mut slot_buf = Vec::new();
                                self.process_include(
                                    *fragment,
                                    &mut slot_buf,
                                    dispatch_fragment_request,
                                    process_fragment_response,
                                )?;
                                buf[slot] = Some(Bytes::from(slot_buf));
                                // dca="esi" may push new items onto self.queue;
                                // the outer while picks them up next iteration.
                            }
                        }
                    }

                    QueuedElement::Try {
                        attempt_elements,
                        except_elements,
                    } => {
                        // Reserve one outer slot for the assembled output.
                        let outer_slot = buf.len();
                        buf.push(None);

                        let tracker_idx = try_trackers.len();
                        try_trackers.push(TryBlockTracker {
                            outer_slot,
                            attempts: Vec::with_capacity(attempt_elements.len()),
                            except_elements,
                            pending_count: 0,
                        });

                        // Walk each attempt through DocumentHandler to
                        // dispatch includes, then flatten results into buf.
                        for (attempt_idx, attempt_elems) in attempt_elements.into_iter().enumerate()
                        {
                            try_trackers[tracker_idx].attempts.push(AttemptTracker {
                                buf_slots: Vec::new(),
                                failed: false,
                            });

                            let mut pre_buf: Vec<u8> = Vec::new();
                            let mut pre_failed = false;
                            self.execute_isolated(
                                &attempt_elems,
                                &mut pre_buf,
                                dispatch_fragment_request,
                                process_fragment_response,
                                |this, pre_out| {
                                    // Static content before the first include.
                                    if !pre_out.is_empty() {
                                        let slot = buf.len();
                                        buf.push(Some(Bytes::from(pre_out.clone())));
                                        try_trackers[tracker_idx].attempts[attempt_idx]
                                            .buf_slots
                                            .push(slot);
                                    }

                                    // Remaining queued elements (document order).
                                    while let Some(qe) = this.queue.pop_front() {
                                        match qe {
                                            QueuedElement::Content(bytes) => {
                                                let slot = buf.len();
                                                buf.push(Some(bytes));
                                                try_trackers[tracker_idx].attempts[attempt_idx]
                                                    .buf_slots
                                                    .push(slot);
                                            }

                                            QueuedElement::Include(mut frag) => {
                                                let slot = buf.len();
                                                buf.push(None);
                                                try_trackers[tracker_idx].attempts[attempt_idx]
                                                    .buf_slots
                                                    .push(slot);

                                                let pc = std::mem::replace(
                                                    &mut frag.pending_fragment,
                                                    PendingFragmentContent::NoContent,
                                                );
                                                match pc {
                                                    PendingFragmentContent::PendingRequest(req) => {
                                                        let key = Self::make_request_key(&frag.req);
                                                        url_map.entry(key).or_default().push_back(
                                                            SlotEntry {
                                                                buf_slot: slot,
                                                                fragment: frag,
                                                                try_info: Some((
                                                                    tracker_idx,
                                                                    attempt_idx,
                                                                )),
                                                            },
                                                        );
                                                        pending.push(*req);
                                                        try_trackers[tracker_idx].pending_count +=
                                                            1;
                                                    }
                                                    ready => {
                                                        frag.pending_fragment = ready;
                                                        let mut slot_buf = Vec::new();
                                                        if this
                                                            .process_include(
                                                                *frag,
                                                                &mut slot_buf,
                                                                dispatch_fragment_request,
                                                                process_fragment_response,
                                                            )
                                                            .is_err()
                                                        {
                                                            pre_failed = true;
                                                        }
                                                        buf[slot] = Some(Bytes::from(slot_buf));
                                                    }
                                                }
                                            }

                                            QueuedElement::Try {
                                                attempt_elements: nested_attempts,
                                                except_elements: nested_except,
                                            } => {
                                                // Nested try: process synchronously.
                                                let slot = buf.len();
                                                buf.push(None);
                                                try_trackers[tracker_idx].attempts[attempt_idx]
                                                    .buf_slots
                                                    .push(slot);
                                                let mut slot_buf = Vec::new();
                                                this.process_try_block(
                                                    nested_attempts,
                                                    &nested_except,
                                                    &mut slot_buf,
                                                    dispatch_fragment_request,
                                                    process_fragment_response,
                                                )?;
                                                buf[slot] = Some(Bytes::from(slot_buf));
                                            }
                                        }
                                    }
                                    Ok(())
                                },
                            )?;

                            if pre_failed {
                                try_trackers[tracker_idx].attempts[attempt_idx].failed = true;
                            }
                        }

                        // If no includes are pending, assemble immediately.
                        if try_trackers[tracker_idx].pending_count == 0 {
                            Self::assemble_try_block(
                                self,
                                tracker_idx,
                                &mut try_trackers,
                                &mut buf,
                                dispatch_fragment_request,
                                process_fragment_response,
                            )?;
                        }
                    }
                }
            }

            // ------------------------------------------------------------------
            // Step 2: flush consecutive ready slots at next_out.
            // ------------------------------------------------------------------
            while next_out < buf.len() {
                match &buf[next_out] {
                    Some(bytes) => {
                        output_writer.write_all(bytes)?;
                        buf[next_out] = Some(Bytes::new()); // release allocation
                        next_out += 1;
                    }
                    None => break, // head slot still waiting
                }
            }

            // ------------------------------------------------------------------
            // Step 3: done when nothing is pending.
            // ------------------------------------------------------------------
            if pending.is_empty() {
                break;
            }

            // ------------------------------------------------------------------
            // Step 4: wait for the next completed request from the shared pool.
            // ------------------------------------------------------------------
            let (result, remaining) = select(pending);
            pending = remaining;

            // ------------------------------------------------------------------
            // Step 5: correlate the response with its SlotEntry and act.
            //
            // Success -> Response::get_backend_request() carries the sent URL.
            // Failure -> SendError::into_sent_req() recovers the URL; a 500 is
            //            synthesised so existing alt/onerror logic is unchanged.
            // ------------------------------------------------------------------
            let (key, completed_content) = match result {
                Ok(resp) => {
                    let key = resp
                        .get_backend_request()
                        .map(Self::make_request_key)
                        .ok_or_else(|| {
                            ESIError::InternalError(
                                "drain_queue: response missing backend request for correlation"
                                    .into(),
                            )
                        })?;
                    (
                        key,
                        PendingFragmentContent::CompletedRequest(Box::new(resp)),
                    )
                }
                Err(e) => {
                    let req = e.into_sent_req();
                    let key = Self::make_request_key(&req);
                    debug!(
                        "Fragment request to {} {} failed; triggering alt/onerror handling",
                        key.method, key.url
                    );
                    (
                        key,
                        PendingFragmentContent::CompletedRequest(Box::new(Response::from_status(
                            StatusCode::INTERNAL_SERVER_ERROR,
                        ))),
                    )
                }
            };

            let entry = url_map
                .get_mut(&key)
                .and_then(VecDeque::pop_front)
                .ok_or_else(|| {
                    ESIError::InternalError(format!(
                        "drain_queue: no in-flight fragment for {}/{}",
                        key.method, key.url
                    ))
                })?;

            let SlotEntry {
                buf_slot,
                mut fragment,
                try_info,
            } = entry;

            match try_info {
                // -------------------------------------------------------
                // Bare <esi:include>: fill the buf slot directly.
                // -------------------------------------------------------
                None => {
                    fragment.pending_fragment = completed_content;
                    let mut slot_buf = Vec::new();
                    self.process_include(
                        *fragment,
                        &mut slot_buf,
                        dispatch_fragment_request,
                        process_fragment_response,
                    )?;
                    buf[buf_slot] = Some(Bytes::from(slot_buf));
                    // dca="esi" may push new QueuedElements onto self.queue.
                    // Loop back to Step 1 to assign them slots.
                }

                // -------------------------------------------------------
                // Include inside a <esi:try> attempt: fill the buf slot,
                // then check if the entire try block is now resolved.
                // -------------------------------------------------------
                Some((tracker_idx, attempt_idx)) => {
                    fragment.pending_fragment = completed_content;
                    let mut slot_buf = Vec::new();
                    let include_failed = self
                        .process_include(
                            *fragment,
                            &mut slot_buf,
                            dispatch_fragment_request,
                            process_fragment_response,
                        )
                        .is_err();
                    buf[buf_slot] = Some(Bytes::from(slot_buf));

                    if include_failed {
                        try_trackers[tracker_idx].attempts[attempt_idx].failed = true;
                    }
                    try_trackers[tracker_idx].pending_count -= 1;

                    if try_trackers[tracker_idx].pending_count == 0 {
                        Self::assemble_try_block(
                            self,
                            tracker_idx,
                            &mut try_trackers,
                            &mut buf,
                            dispatch_fragment_request,
                            process_fragment_response,
                        )?;
                    }
                    // dca="esi" inside a try-attempt promotes sub-includes
                    // to outer slots.  Loop back to Step 1.
                }
            }
        }

        // Final flush: every slot must be ready at this point.
        while next_out < buf.len() {
            match &buf[next_out] {
                Some(bytes) => {
                    output_writer.write_all(bytes)?;
                    next_out += 1;
                }
                None => {
                    return Err(ESIError::InternalError(
                        "drain_queue: slot still pending after all requests resolved".into(),
                    ));
                }
            }
        }

        Ok(())
    }

    /// Assemble a fully-resolved try block: concatenate successful attempt
    /// content from `buf` slots, clear inner slots, and set the outer slot.
    fn assemble_try_block(
        &mut self,
        tracker_idx: usize,
        try_trackers: &mut [TryBlockTracker],
        buf: &mut [Option<Bytes>],
        dispatch_fragment_request: &FragmentRequestDispatcher,
        process_fragment_response: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        let mut any_failed = false;
        let mut output: Vec<u8> = Vec::new();

        for attempt in &try_trackers[tracker_idx].attempts {
            if attempt.failed {
                any_failed = true;
                // Clear failed attempt's inner slots so Step 2 skips them.
                for &slot_idx in &attempt.buf_slots {
                    buf[slot_idx] = Some(Bytes::new());
                }
            } else {
                for &slot_idx in &attempt.buf_slots {
                    if let Some(bytes) = &buf[slot_idx] {
                        output.extend_from_slice(bytes);
                    }
                    // Clear inner slot so Step 2 flushes it as a no-op.
                    buf[slot_idx] = Some(Bytes::new());
                }
            }
        }

        if any_failed {
            let except_elements = std::mem::take(&mut try_trackers[tracker_idx].except_elements);
            if !except_elements.is_empty() {
                let except_buf = self.process_try_task(
                    &except_elements,
                    dispatch_fragment_request,
                    process_fragment_response,
                )?;
                output.extend_from_slice(&except_buf);
            }
        }

        buf[try_trackers[tracker_idx].outer_slot] = Some(Bytes::from(output));
        Ok(())
    }

    /// Process a try block: execute ALL attempts in document order (they are
    /// independent statements), then run the except clause if any failed.
    fn process_try_block(
        &mut self,
        attempt_elements: Vec<Vec<Element>>,
        except_elements: &[Element],
        output_writer: &mut impl Write,
        dispatcher: &FragmentRequestDispatcher,
        processor: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        let mut any_failed = false;
        for attempt in attempt_elements {
            match self.process_try_task(&attempt, dispatcher, processor) {
                Ok(buffer) => output_writer.write_all(&buffer)?,
                Err(_) => any_failed = true,
            }
        }
        if any_failed {
            let buf = self.process_try_task(except_elements, dispatcher, processor)?;
            output_writer.write_all(&buf)?;
        }
        Ok(())
    }

    /// Execute a `DocumentHandler` with an isolated queue.
    ///
    /// Saves `self.queue`, runs the handler writing into `output`, executes the
    /// provided `after` closure (which can consume the temporary queue), then
    /// restores the saved queue.
    fn execute_isolated<R, W: Write>(
        &mut self,
        elements: &[Element],
        output: &mut W,
        dispatcher: &FragmentRequestDispatcher,
        processor: Option<&FragmentResponseProcessor>,
        after: impl FnOnce(&mut Self, &mut W) -> Result<R>,
    ) -> Result<R> {
        let saved_queue = std::mem::take(&mut self.queue);

        {
            let mut handler = DocumentHandler {
                processor: self,
                output,
                dispatch_fragment_request: dispatcher,
                fragment_response_handler: processor,
            };
            for elem in elements {
                handler.process(elem)?;
            }
        }

        let result = after(self, output);

        // Always restore the outer queue, even if `after` failed.
        self.queue = saved_queue;
        result
    }

    /// Execute a list of raw ESI elements in document order into a fresh buffer.
    ///
    /// Elements are processed sequentially through a `DocumentHandler`:
    ///   - Text / Html / Expr and complex tags (Choose, Foreach, Assign, …)
    ///     execute immediately, writing into `buffer` directly when no
    ///     in-flight includes precede them, or into `self.queue` as `Content`
    ///     when an include is already queued (preserving document order).
    ///   - `<esi:include>` is dispatched asynchronously at the exact point it
    ///     is reached, **after** all preceding assigns have updated the context.
    ///
    /// After all elements have been walked, any queued includes are drained in
    /// document order (blocking wait per include).
    fn process_try_task(
        &mut self,
        elements: &[Element],
        dispatcher: &FragmentRequestDispatcher,
        processor: Option<&FragmentResponseProcessor>,
    ) -> Result<Vec<u8>> {
        let mut buffer = Vec::new();
        self.execute_isolated(elements, &mut buffer, dispatcher, processor, |this, out| {
            this.drain_queue(out, dispatcher, processor)?;
            Ok(())
        })?;

        Ok(buffer)
    }

    /// Process an include from the queue (wait and write, handle alt)
    fn process_include(
        &mut self,
        fragment: Fragment,
        output_writer: &mut impl Write,
        dispatch_fragment_request: &FragmentRequestDispatcher,
        process_fragment_response: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        let continue_on_error = fragment.metadata.continue_on_error;

        // Wait for response
        let response = fragment.pending_fragment.wait()?;

        // Apply processor if provided (only clone the request when a processor exists)
        let final_response = if let Some(proc) = process_fragment_response {
            let mut req_for_processor = fragment.req.clone_without_body();
            proc(&mut req_for_processor, response)?
        } else {
            response
        };

        // Track TTL for rendered document caching
        if final_response.get_status().is_success()
            && (self.configuration.cache.is_rendered_cacheable
                || self.configuration.cache.rendered_cache_control)
        {
            let ttl = if let Some(override_ttl) = fragment.metadata.ttl_override {
                debug!("Using TTL override from include tag: {override_ttl} seconds");
                Some(override_ttl)
            } else {
                match cache::calculate_ttl(&final_response, &self.configuration.cache) {
                    Ok(Some(ttl)) => {
                        debug!("Calculated TTL from response: {ttl} seconds");
                        Some(ttl)
                    }
                    Ok(None) => {
                        debug!("Response not cacheable (private/no-cache/set-cookie)");
                        self.ctx.mark_document_uncacheable();
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

        // Check if successful
        if final_response.get_status().is_success() {
            let body_bytes = final_response.into_body_bytes();
            self.process_fragment_body(
                body_bytes,
                fragment.metadata.dca,
                output_writer,
                dispatch_fragment_request,
                process_fragment_response,
            )?;
            Ok(())
        } else if let Some(alt_src) = fragment.alt_bytes {
            // Try alt - reuse pre-evaluated params
            debug!("Main request failed, trying alt");
            let alt_req = build_fragment_request(
                self.ctx.get_request().clone_without_body(),
                &alt_src,
                &fragment.metadata,
                &self.configuration,
            )?;

            let alt_req_without_body = alt_req.clone_without_body();
            match dispatch_fragment_request(alt_req_without_body, fragment.metadata.maxwait) {
                Ok(alt_pending) => {
                    let alt_response = alt_pending.wait()?;
                    let final_alt = if let Some(proc) = process_fragment_response {
                        let mut alt_req_for_proc = alt_req.clone_without_body();
                        proc(&mut alt_req_for_proc, alt_response)?
                    } else {
                        alt_response
                    };

                    let body_bytes = final_alt.into_body_bytes();
                    self.process_fragment_body(
                        body_bytes,
                        fragment.metadata.dca,
                        output_writer,
                        dispatch_fragment_request,
                        process_fragment_response,
                    )?;
                    Ok(())
                }
                Err(_) if continue_on_error => {
                    output_writer.write_all(self.fragment_req_failed())?;
                    Ok(())
                }
                Err(_) => Err(ESIError::FragmentRequestError(
                    "both main and alt failed".into(),
                )),
            }
        } else if continue_on_error {
            output_writer.write_all(self.fragment_req_failed())?;
            Ok(())
        } else {
            Err(ESIError::FragmentRequestError(format!(
                "fragment request failed with status: {}",
                final_response.get_status()
            )))
        }
    }

    /// Process fragment body based on dca mode
    /// - dca="esi": Parse and process content as ESI
    /// - dca="none": Write raw content
    fn process_fragment_body(
        &mut self,
        body_bytes: Vec<u8>,
        dca_mode: DcaMode,
        output_writer: &mut impl Write,
        dispatcher: &FragmentRequestDispatcher,
        process_fragment_response: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        if dca_mode == DcaMode::Esi {
            // Parse and process the content as ESI
            let body_as_bytes = Bytes::from(body_bytes);
            let (rest, elements) = parser::parse_remainder(&body_as_bytes).map_err(|e| {
                ESIError::ParseError(format!("failed to parse fragment with dca=esi: {e}",))
            })?;

            if !rest.is_empty() {
                return Err(ESIError::ParseError(
                    "incomplete parse of fragment with dca=esi".into(),
                ));
            }

            // Process each element in the current namespace
            let mut handler = DocumentHandler {
                processor: self,
                output: output_writer,
                dispatch_fragment_request: dispatcher,
                fragment_response_handler: process_fragment_response,
            };
            for element in elements {
                if matches!(handler.process(&element)?, Flow::Break) {
                    return Ok(()); // Break from foreach, stop processing
                }
            }
        } else {
            // dca="none" (default): Write raw content
            output_writer.write_all(&body_bytes)?;
        }
        Ok(())
    }
}

/// Placeholder HTML comment written when a fragment could not be fetched and `onerror="continue"`.
/// Only emitted for HTML content (when `is_escaped_content` is true).
const FRAGMENT_REQUEST_FAILED: &[u8] = b"<!-- fragment request failed -->";

/// Evaluate an [`Expr`] to a [`Bytes`] value.
///
/// Free function (not a `Processor` method) so callers can independently borrow other
/// `Processor` fields alongside `ctx`.
fn eval_expr_to_bytes(expr: &Expr, ctx: &mut EvalContext) -> Result<Bytes> {
    let result = expression::eval_expr(expr, ctx)?;
    Ok(result.to_bytes())
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
        .map_err(|e| ESIError::FragmentRequestError(format!("failed to create backend: {e}")))?;

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
    config: &Configuration,
) -> Result<Request> {
    // Convert Bytes to str for URL parsing
    let url_str = std::str::from_utf8(url)
        .map_err(|_| ESIError::InvalidFragmentConfig("invalid UTF-8 in URL".to_string()))?;

    let escaped_url = if config.is_escaped_content {
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
                return Err(ESIError::InvalidRequestUrl(escaped_url.into_owned()));
            }
        }
    } else {
        request.set_url(match Url::parse(&escaped_url) {
            Ok(url) => url,
            Err(_err) => {
                return Err(ESIError::InvalidRequestUrl(escaped_url.into_owned()));
            }
        });
    }

    let hostname = request.get_url().host().expect("no host").to_string();

    request.set_header(header::HOST, &hostname);

    // Set HTTP method (default is GET) - use pre-evaluated value
    if let Some(method_bytes) = &metadata.method {
        let method_str = std::str::from_utf8(method_bytes)
            .map_err(|_| ESIError::InvalidFragmentConfig("invalid UTF-8 in method".to_string()))?
            .to_uppercase();

        match method_str.as_str() {
            "GET" => request.set_method(Method::GET),
            "POST" => request.set_method(Method::POST),
            _ => {
                return Err(ESIError::InvalidFragmentConfig(format!(
                    "unsupported HTTP method: {method_str}"
                )))
            }
        }
    }

    // Set POST body if provided - use pre-evaluated value
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

    // 2. Set headers (replace existing) - use pre-evaluated values
    for (name, value) in &metadata.setheaders {
        request.set_header(name, value.as_ref());
    }

    // 3. Append headers (add to existing) - use pre-evaluated values
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
