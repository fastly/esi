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
pub use crate::parser::parse;

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

// Process parser chunks directly to output - with fragment request support
fn process_chunk_to_output(
    chunk: parser_types::Chunk,
    ctx: &mut EvalContext,
    output_writer: &mut impl Write,
    original_request_metadata: &Request,
    dispatch_fragment_request: Option<&FragmentRequestDispatcher>,
    is_escaped_content: bool,
) -> Result<()> {
    use parser_types::{Chunk, Tag as NomTag};

    eprintln!("DEBUG: Processing chunk: {:?}", chunk);
    match chunk {
        Chunk::Text(text) => {
            output_writer.write_all(text.as_bytes())?;
            Ok(())
        }
        Chunk::Html(html) => {
            output_writer.write_all(html.as_bytes())?;
            Ok(())
        }
        Chunk::Expr(expr) => {
            // Evaluate the expression using the full evaluator and write as text
            match expression::eval_expr(expr, ctx) {
                Ok(result) => {
                    // Don't output anything for Null values
                    if !matches!(result, expression::Value::Null) {
                        let result_str = result.to_string();
                        if !result_str.is_empty() {
                            output_writer.write_all(result_str.as_bytes())?;
                        }
                    }
                }
                Err(e) => {
                    debug!("Expression evaluation failed: {:?}", e);
                }
            }
            Ok(())
        }
        Chunk::Esi(tag) => {
            match tag {
                NomTag::Assign { name, value } => {
                    // Handle esi:assign tags - evaluate the value expression and set variable
                    //First, check if the value is a quoted string literal and strip quotes
                    let trimmed = value.trim();
                    let unquoted_value = if trimmed.starts_with('\'')
                        && trimmed.ends_with('\'')
                        && trimmed.len() >= 2
                    {
                        // Single-quoted string: strip quotes
                        trimmed[1..trimmed.len() - 1].to_string()
                    } else if trimmed.starts_with('"')
                        && trimmed.ends_with('"')
                        && trimmed.len() >= 2
                    {
                        // Double-quoted string: strip quotes
                        trimmed[1..trimmed.len() - 1].to_string()
                    } else {
                        value.clone()
                    };

                    // Evaluate the value as an ESI expression using parser
                    let evaluated_value = crate::parser::parse_expression(&unquoted_value)
                        .map(|(_, expr)| crate::expression::eval_expr(expr, ctx))
                        .ok()
                        .and_then(|r| r.ok())
                        .map(|v| v.to_string())
                        .unwrap_or(unquoted_value);

                    ctx.set_variable(
                        &name,
                        None,
                        crate::expression::Value::Text(evaluated_value.into()),
                    );
                    Ok(())
                }
                NomTag::Include {
                    src,
                    alt,
                    continue_on_error,
                } => {
                    if let Some(dispatcher) = dispatch_fragment_request {
                        // Handle esi:include tags - evaluate expressions and build fragment request
                        debug!("Handling <esi:include> tag with src: {}", src);

                        // Always interpolate src
                        let interpolated_src = try_evaluate_interpolated_string(&src, ctx)?;

                        // Build fragment request
                        let req = build_fragment_request(
                            original_request_metadata.clone_without_body(),
                            &interpolated_src,
                            is_escaped_content,
                        )?;

                        match dispatcher(req) {
                            Ok(pending_content) => {
                                // Process the fragment content directly
                                match pending_content {
                                    crate::PendingFragmentContent::CompletedRequest(response) => {
                                        // Write the response body directly to output
                                        let body_bytes = response.into_body_bytes();
                                        let body_str = std::str::from_utf8(&body_bytes)
                                            .unwrap_or("<!-- invalid utf8 -->");
                                        output_writer.write_all(body_str.as_bytes())?;
                                    }
                                    crate::PendingFragmentContent::PendingRequest(pending) => {
                                        // This shouldn't happen in Phase 3 since we wait for all requests in Phase 2,
                                        // but handle it gracefully by waiting for the request now
                                        let response = pending.wait().map_err(|e| {
                                            ESIError::ExpressionError(format!(
                                                "Fragment request wait failed: {}",
                                                e
                                            ))
                                        })?;
                                        let body_bytes = response.into_body_bytes();
                                        let body_str = std::str::from_utf8(&body_bytes)
                                            .unwrap_or("<!-- invalid utf8 -->");
                                        output_writer.write_all(body_str.as_bytes())?;
                                    }
                                    crate::PendingFragmentContent::NoContent => {
                                        // No content to output
                                    }
                                }
                            }
                            Err(err) => {
                                if continue_on_error {
                                    // Try alt if available
                                    if let Some(alt_src) = &alt {
                                        let interpolated_alt =
                                            try_evaluate_interpolated_string(alt_src, ctx)?;
                                        let alt_req = build_fragment_request(
                                            original_request_metadata.clone_without_body(),
                                            &interpolated_alt,
                                            is_escaped_content,
                                        )?;
                                        match dispatcher(alt_req) {
                                            Ok(pending_content) => {
                                                match pending_content {
                                                    crate::PendingFragmentContent::CompletedRequest(response) => {
                                                        let body_bytes = response.into_body_bytes();
                                                        let body_str = std::str::from_utf8(&body_bytes).unwrap_or("<!-- invalid utf8 -->");
                                                        output_writer.write_all(body_str.as_bytes())?;
                                                    }
                                                    crate::PendingFragmentContent::PendingRequest(_) => {
                                                        output_writer.write_all(b"<!-- pending alt request -->")?;
                                                    }
                                                    crate::PendingFragmentContent::NoContent => {
                                                        // No alt content to output
                                                    }
                                                }
                                            }
                                            Err(_) => {
                                                // Both main and alt failed, but continue-on-error is set
                                                output_writer.write_all(
                                                    b"<!-- fragment request failed -->",
                                                )?;
                                            }
                                        }
                                    } else {
                                        // No alt, but continue on error
                                        output_writer
                                            .write_all(b"<!-- fragment request failed -->")?;
                                    }
                                } else {
                                    return Err(ESIError::ExpressionError(format!(
                                        "Fragment request failed: {}",
                                        err
                                    )));
                                }
                            }
                        }
                    } else {
                        // No fragment dispatcher available, output placeholder
                        output_writer.write_all(b"<!-- ESI include not supported -->")?;
                    }
                    Ok(())
                }
                NomTag::Choose {
                    when_branches,
                    otherwise_events,
                } => {
                    // Handle esi:choose/when/otherwise logic - ported from main branch
                    let mut chose_branch = false;
                    for (when_tag, events) in when_branches {
                        if let NomTag::When { test, match_name } = when_tag {
                            if let Some(match_name) = match_name {
                                ctx.set_match_name(&match_name);
                            }
                            let (_, expr) =
                                crate::parser::parse_expression(&test).map_err(|e| {
                                    ExecutionError::ExpressionError(format!(
                                        "Failed to parse test expression: {e}"
                                    ))
                                })?;
                            let result = crate::expression::eval_expr(expr, ctx)?;
                            if result.to_bool() {
                                chose_branch = true;
                                for chunk in events {
                                    process_chunk_to_output(
                                        chunk,
                                        ctx,
                                        output_writer,
                                        original_request_metadata,
                                        dispatch_fragment_request,
                                        is_escaped_content,
                                    )?;
                                }
                                break;
                            }
                        }
                    }

                    if !chose_branch {
                        for chunk in otherwise_events {
                            process_chunk_to_output(
                                chunk,
                                ctx,
                                output_writer,
                                original_request_metadata,
                                dispatch_fragment_request,
                                is_escaped_content,
                            )?;
                        }
                    }
                    Ok(())
                }
                NomTag::Try {
                    attempt_events,
                    except_events,
                } => {
                    // Try processing attempt blocks - if any fail, process except block
                    let mut any_succeeded = false;
                    for attempt_chunks in attempt_events {
                        let mut attempt_output = Vec::new();
                        let attempt_result = (|| {
                            for chunk in attempt_chunks {
                                process_chunk_to_output(
                                    chunk,
                                    ctx,
                                    &mut attempt_output,
                                    original_request_metadata,
                                    dispatch_fragment_request,
                                    is_escaped_content,
                                )?;
                            }
                            Ok::<(), ExecutionError>(())
                        })();

                        if attempt_result.is_ok() {
                            // Attempt succeeded - write its output and we're done
                            output_writer.write_all(&attempt_output)?;
                            any_succeeded = true;
                            break;
                        }
                        // Attempt failed - try next attempt
                    }

                    // If all attempts failed, process except block
                    if !any_succeeded {
                        for chunk in except_events {
                            process_chunk_to_output(
                                chunk,
                                ctx,
                                output_writer,
                                original_request_metadata,
                                dispatch_fragment_request,
                                is_escaped_content,
                            )?;
                        }
                    }
                    Ok(())
                }
                NomTag::Vars { .. } => {
                    // <esi:vars> is handled by the parser - it returns chunks directly, never creates a Tag::Vars
                    // If we see this, it's a parser bug. Just skip it.
                    debug!("Unexpected Tag::Vars - parser should return chunks directly for <esi:vars>");
                    Ok(())
                }
                NomTag::When { .. }
                | NomTag::Attempt(_)
                | NomTag::Except(_)
                | NomTag::Otherwise => {
                    // These tags should only appear inside Choose/Try blocks and are handled there
                    // If they appear standalone, it's likely a parser bug or malformed ESI
                    debug!(
                        "Unexpected standalone {:?} tag - should be inside Choose/Try block",
                        tag
                    );
                    Ok(())
                }
            }
        }
    }
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

/// Represents a fragment that needs to be fetched
struct Fragment {
    /// Index in the chunks array where this fragment should be inserted
    chunk_index: usize,
    /// The original request for this fragment (needed for process_fragment_response callback)
    request: Request,
    /// The pending fragment content (request or already completed)
    pending_content: PendingFragmentContent,
    /// Alternative source URL if main request fails (built lazily only if needed)
    alt: Option<String>,
    /// Whether to continue processing if this fragment fails
    continue_on_error: bool,
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
/// let request = Request::get("http://example.com/");
///
/// // Initialize the Processor with optional request metadata
/// let processor = Processor::new(Some(request), config);
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

    /// Process an ESI document using the nom parser, handling includes and directives
    ///
    /// This method uses a three-phase approach to enable **concurrent fragment fetching**:
    ///
    /// **Phase 1**: Parse the document and collect all fragment requests. This allows
    /// us to identify all `<esi:include>` tags upfront.
    ///
    /// **Phase 2**: Dispatch all fragment requests concurrently using Fastly's async
    /// request capabilities. This minimizes latency by fetching fragments in parallel
    /// rather than sequentially.
    ///
    /// **Phase 3**: Process chunks and stream output, inserting the resolved fragment
    /// responses in their correct positions.
    ///
    /// Processes ESI directives while streaming content to the output writer. Handles:
    /// - ESI includes with concurrent fragment fetching
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
        self,
        mut src_document: impl BufRead,
        output_writer: &mut impl Write,
        dispatch_fragment_request: Option<&FragmentRequestDispatcher>,
        process_fragment_response: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {
        // If there is a source request to mimic, copy its metadata, otherwise use a default request.
        let original_request_metadata = self.original_request_metadata.as_ref().map_or_else(
            || Request::new(Method::GET, "http://localhost"),
            Request::clone_without_body,
        );

        // Read the entire document into a string for nom parser
        let mut doc_content = String::new();
        src_document
            .read_to_string(&mut doc_content)
            .map_err(ESIError::WriterError)?;

        // Parse the document using nom parser
        let (remaining, chunks) = parser::parse(&doc_content)
            .map_err(|e| ESIError::ExpressionError(format!("Nom parser error: {:?}", e)))?;

        eprintln!("DEBUG: Parser returned {} chunks", chunks.len());
        for (i, chunk) in chunks.iter().enumerate() {
            eprintln!("DEBUG: Chunk[{}]: {:?}", i, chunk);
        }

        // Log warning if parser didn't consume everything (may indicate unsupported features)
        if !remaining.is_empty() {
            debug!(
                "Parser did not consume all input. Remaining: '{}'",
                remaining.chars().take(100).collect::<String>()
            );
            eprintln!("DEBUG: Parser remaining: {:?}", remaining);
        }

        // context for the interpreter
        let mut ctx = EvalContext::new();
        ctx.set_request(original_request_metadata.clone_without_body());

        // PHASE 1: Collect all fragment requests while doing a first pass
        // This allows us to dispatch all requests concurrently
        let mut fragments = Vec::new();

        // Use the provided dispatcher or fall back to the default
        let dispatcher = dispatch_fragment_request.unwrap_or(&default_fragment_dispatcher);

        for (idx, chunk) in chunks.iter().enumerate() {
            if let parser_types::Chunk::Esi(parser_types::Tag::Include {
                src,
                alt,
                continue_on_error,
            }) = chunk
            {
                // Interpolate the src URL
                let interpolated_src = try_evaluate_interpolated_string(src, &mut ctx)?;

                // Build and dispatch the fragment request
                let req = build_fragment_request(
                    original_request_metadata.clone_without_body(),
                    &interpolated_src,
                    self.configuration.is_escaped_content,
                )?;

                match dispatcher(req.clone_without_body()) {
                    Ok(pending_content) => {
                        fragments.push(Fragment {
                            chunk_index: idx,
                            request: req,
                            pending_content,
                            alt: alt.clone(),
                            continue_on_error: *continue_on_error,
                        });
                    }
                    Err(err) => {
                        // Main request failed during dispatch
                        // Try alt if available
                        if let Some(alt_src) = alt {
                            let interpolated_alt =
                                try_evaluate_interpolated_string(alt_src, &mut ctx)?;
                            let alt_req = build_fragment_request(
                                original_request_metadata.clone_without_body(),
                                &interpolated_alt,
                                self.configuration.is_escaped_content,
                            )?;

                            match dispatcher(alt_req.clone_without_body()) {
                                Ok(alt_pending) => {
                                    fragments.push(Fragment {
                                        chunk_index: idx,
                                        request: alt_req,
                                        pending_content: alt_pending,
                                        alt: None, // Alt already used
                                        continue_on_error: *continue_on_error,
                                    });
                                }
                                Err(_) => {
                                    // Both main and alt failed
                                    if *continue_on_error {
                                        fragments.push(Fragment {
                                            chunk_index: idx,
                                            request: req,
                                            pending_content: PendingFragmentContent::NoContent,
                                            alt: None,
                                            continue_on_error: *continue_on_error,
                                        });
                                    } else {
                                        return Err(ESIError::ExpressionError(format!(
                                            "Fragment dispatch failed: {}",
                                            err
                                        )));
                                    }
                                }
                            }
                        } else {
                            // No alt, check if we should continue
                            if *continue_on_error {
                                fragments.push(Fragment {
                                    chunk_index: idx,
                                    request: req,
                                    pending_content: PendingFragmentContent::NoContent,
                                    alt: None,
                                    continue_on_error: *continue_on_error,
                                });
                            } else {
                                return Err(ESIError::ExpressionError(format!(
                                    "Fragment dispatch failed: {}",
                                    err
                                )));
                            }
                        }
                    }
                }
            }
        }

        // PHASE 2: Wait for all pending fragment requests to complete
        // This allows concurrent fetching instead of sequential
        let mut fragment_responses: std::collections::HashMap<usize, Result<Vec<u8>>> =
            std::collections::HashMap::new();

        for mut fragment_info in fragments {
            let response_result = fragment_info.pending_content.wait();

            // Apply the fragment response processor if provided
            let processed_response = match response_result {
                Ok(resp) => {
                    if let Some(processor) = process_fragment_response {
                        processor(&mut fragment_info.request, resp)
                    } else {
                        Ok(resp)
                    }
                }
                Err(e) => Err(e),
            };

            // If main request failed and we have an alt, try the alt
            let final_response = if processed_response.is_err() && fragment_info.alt.is_some() {
                let alt = fragment_info.alt.unwrap();
                let interpolated_alt = try_evaluate_interpolated_string(&alt, &mut ctx)?;
                let mut alt_req = build_fragment_request(
                    original_request_metadata.clone_without_body(),
                    &interpolated_alt,
                    self.configuration.is_escaped_content,
                )?;

                match dispatcher(alt_req.clone_without_body()) {
                    Ok(alt_pending) => {
                        let alt_resp = alt_pending.wait()?;
                        // Also process the alt response
                        if let Some(processor) = process_fragment_response {
                            processor(&mut alt_req, alt_resp)
                        } else {
                            Ok(alt_resp)
                        }
                    }
                    Err(e) => {
                        if fragment_info.continue_on_error {
                            Ok(Response::from_status(StatusCode::NO_CONTENT))
                        } else {
                            Err(ESIError::ExpressionError(format!(
                                "Alt fragment failed: {}",
                                e
                            )))
                        }
                    }
                }
            } else {
                processed_response
            };

            // Convert response to bytes immediately
            let body_bytes = match final_response {
                Ok(response) => Ok(response.into_body_bytes()),
                Err(e) => {
                    if fragment_info.continue_on_error {
                        Ok(Vec::new()) // Empty body for failed fragments with continue_on_error
                    } else {
                        Err(e)
                    }
                }
            };

            fragment_responses.insert(fragment_info.chunk_index, body_bytes);
        }

        // PHASE 3: Process chunks and output, using the resolved fragment responses
        for (idx, chunk) in chunks.into_iter().enumerate() {
            // Check if this chunk is a fragment that we fetched
            if let Some(body_result) = fragment_responses.remove(&idx) {
                match body_result {
                    Ok(body_bytes) => {
                        // Write the fragment response body to output
                        let body_str =
                            std::str::from_utf8(&body_bytes).unwrap_or("<!-- invalid utf8 -->");
                        output_writer.write_all(body_str.as_bytes())?;
                    }
                    Err(err) => {
                        // Fragment failed and continue_on_error was false
                        return Err(err);
                    }
                }
            } else {
                // Not a fragment - process normally
                process_chunk_to_output(
                    chunk,
                    &mut ctx,
                    output_writer,
                    &original_request_metadata,
                    None, // Don't dispatch fragments here - already done in phase 1
                    self.configuration.is_escaped_content,
                )?;
            }
        }

        Ok(())
    }
}

// ============================================================================
// Helper Functions
// ============================================================================

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
    let chunks = match crate::parser::parse_interpolated_string(input) {
        Ok((_, chunks)) => chunks,
        Err(_) => {
            // If parsing fails, treat the whole input as text
            segment_handler(input.to_string())?;
            return Ok(());
        }
    };

    // Process each chunk
    for chunk in chunks {
        match chunk {
            parser_types::Chunk::Text(text) => {
                segment_handler(text.to_string())?;
            }
            parser_types::Chunk::Expr(expr) => {
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
