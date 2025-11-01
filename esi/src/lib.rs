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

//
fn fetch_elements(
    element: parser_types::Element,
    ctx: &mut EvalContext,
    output_writer: &mut impl Write,
    original_request_metadata: &Request,
    dispatch_fragment_request: &FragmentRequestDispatcher,
    process_fragment_response: Option<&FragmentResponseProcessor>,
    is_escaped_content: bool,
) -> Result<()> {
    use parser_types::{Element, Tag};

    eprintln!("DEBUG: Processing element: {:?}", element);
    match element {
        Element::Text(text) => {
            output_writer.write_all(text.as_bytes())?;
            Ok(())
        }
        Element::Html(html) => {
            output_writer.write_all(html.as_bytes())?;
            Ok(())
        }
        Element::Expr(expr) => {
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
        Element::Esi(tag) => {
            match tag {
                Tag::Assign { name, value } => {
                    // Handle esi:assign tags - evaluate the pre-parsed value expression
                    let evaluated_value = match crate::expression::eval_expr(value, ctx) {
                        Ok(val) => val,
                        Err(_) => {
                            // If evaluation fails, use empty string
                            crate::expression::Value::Text("".into())
                        }
                    };

                    ctx.set_variable(&name, None, evaluated_value);
                    Ok(())
                }
                Tag::Include {
                    src,
                    alt,
                    continue_on_error,
                } => {
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

                    match dispatch_fragment_request(req.clone_without_body()) {
                        Ok(pending_content) => {
                            // Wait for the fragment and process it
                            let response = pending_content.wait()?;

                            // Apply process_fragment_response callback if provided
                            let mut req_for_processor = req.clone_without_body();
                            let final_response = if let Some(processor) = process_fragment_response
                            {
                                processor(&mut req_for_processor, response)?
                            } else {
                                response
                            };

                            // Write the response body to output
                            let body_bytes = final_response.into_body_bytes();
                            let body_str =
                                std::str::from_utf8(&body_bytes).unwrap_or("<!-- invalid utf8 -->");
                            output_writer.write_all(body_str.as_bytes())?;
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
                                    match dispatch_fragment_request(alt_req.clone_without_body()) {
                                        Ok(pending_content) => {
                                            // Wait for alt fragment and process it
                                            let response = pending_content.wait()?;

                                            // Apply process_fragment_response callback if provided
                                            let mut alt_req_for_processor =
                                                alt_req.clone_without_body();
                                            let final_response = if let Some(processor) =
                                                process_fragment_response
                                            {
                                                processor(&mut alt_req_for_processor, response)?
                                            } else {
                                                response
                                            };

                                            // Write the alt response body to output
                                            let body_bytes = final_response.into_body_bytes();
                                            let body_str = std::str::from_utf8(&body_bytes)
                                                .unwrap_or("<!-- invalid utf8 -->");
                                            output_writer.write_all(body_str.as_bytes())?;
                                        }
                                        Err(_) => {
                                            // Both main and alt failed, but continue-on-error is set
                                            output_writer
                                                .write_all(b"<!-- fragment request failed -->")?;
                                        }
                                    }
                                } else {
                                    // No alt, but continue on error
                                    output_writer.write_all(b"<!-- fragment request failed -->")?;
                                }
                            } else {
                                return Err(ESIError::ExpressionError(format!(
                                    "Fragment request failed: {}",
                                    err
                                )));
                            }
                        }
                    }
                    Ok(())
                }
                Tag::Choose {
                    when_branches,
                    otherwise_events,
                } => {
                    // Handle esi:choose/when/otherwise logic per ESI spec:
                    // - Evaluate each when branch in order
                    // - Execute only the FIRST when that evaluates to true
                    // - Execute otherwise only if ALL when branches are false
                    let mut chose_branch = false;
                    for when_branch in when_branches {
                        if let Some(match_name) = &when_branch.match_name {
                            ctx.set_match_name(match_name);
                        }
                        // Evaluate the pre-parsed test expression (no need to parse again!)
                        let result = crate::expression::eval_expr(when_branch.test, ctx)?;
                        if result.to_bool() {
                            chose_branch = true;
                            for element in when_branch.content {
                                fetch_elements(
                                    element,
                                    ctx,
                                    output_writer,
                                    original_request_metadata,
                                    dispatch_fragment_request,
                                    process_fragment_response,
                                    is_escaped_content,
                                )?;
                            }
                            break;
                        }
                    }

                    if !chose_branch {
                        for element in otherwise_events {
                            fetch_elements(
                                element,
                                ctx,
                                output_writer,
                                original_request_metadata,
                                dispatch_fragment_request,
                                process_fragment_response,
                                is_escaped_content,
                            )?;
                        }
                    }
                    Ok(())
                }
                Tag::Try {
                    attempt_events,
                    except_events,
                } => {
                    // Try processing attempt blocks - if any fail, process except block
                    let mut any_succeeded = false;
                    for attempt_elements in attempt_events {
                        let mut attempt_output = Vec::new();
                        let attempt_result = (|| {
                            for element in attempt_elements {
                                fetch_elements(
                                    element,
                                    ctx,
                                    &mut attempt_output,
                                    original_request_metadata,
                                    dispatch_fragment_request,
                                    process_fragment_response,
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
                        for element in except_events {
                            fetch_elements(
                                element,
                                ctx,
                                output_writer,
                                original_request_metadata,
                                dispatch_fragment_request,
                                process_fragment_response,
                                is_escaped_content,
                            )?;
                        }
                    }
                    Ok(())
                }
                Tag::Vars { .. } => {
                    // <esi:vars> is handled by the parser - it returns elements directly, never creates a Tag::Vars
                    // If we see this, it's a parser bug. Just skip it.
                    debug!("Unexpected Tag::Vars - parser should return elements directly for <esi:vars>");
                    Ok(())
                }
                Tag::When { .. } | Tag::Attempt(_) | Tag::Except(_) | Tag::Otherwise => {
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
    /// Processes ESI directives while streaming content to the output writer. This method
    /// processes elements **sequentially**, dispatching and waiting for fragments only as they
    /// are encountered during processing. This ensures optimal performance by:
    ///
    /// - Only fetching fragments that are actually needed (not those in unexecuted branches)
    /// - Streaming output as soon as fragments complete
    /// - Not blocking on fragments inside conditional blocks that don't execute
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
        let (remaining, elements) = parser::parse(&doc_content)
            .map_err(|e| ESIError::ExpressionError(format!("Nom parser error: {:?}", e)))?;

        eprintln!("DEBUG: Parser returned {} elements", elements.len());
        for (i, element) in elements.iter().enumerate() {
            eprintln!("DEBUG: Chunk[{}]: {:?}", i, element);
        }

        // Log warning if parser didn't consume everything (may indicate unsupported features)
        if !remaining.is_empty() {
            debug!(
                "Parser did not consume all input. Remaining: '{}'",
                remaining.chars().take(100).collect::<String>()
            );
            eprintln!("DEBUG: Parser remaining: {:?}", remaining);
        }

        // Set up fragment request dispatcher. Use what's provided or use a default
        let dispatch_fragment_request =
            dispatch_fragment_request.unwrap_or(&default_fragment_dispatcher);

        // context for the interpreter
        let mut ctx = EvalContext::new();
        ctx.set_request(original_request_metadata.clone_without_body());

        // Process elements sequentially, dispatching and waiting for fragments only as encountered
        for element in elements {
            fetch_elements(
                element,
                &mut ctx,
                output_writer,
                &original_request_metadata,
                dispatch_fragment_request,
                process_fragment_response,
                self.configuration.is_escaped_content,
            )?;
        }

        Ok(())
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
