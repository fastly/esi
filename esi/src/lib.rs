#![doc = include_str!("../README.md")]

mod config;
// mod document;  // Old quick_xml based code - not used by nom parser
mod error;
mod expression;
mod functions;
mod new_parse;
// mod parse;  // Old quick_xml based code - not used by nom parser
mod parser_types;

use crate::expression::{try_evaluate_interpolated, EvalContext};
use fastly::http::request::PendingRequest;
use fastly::http::{header, Method, StatusCode, Url};
use fastly::{mime, Request, Response};
use log::{debug, error};
use std::io::{BufRead, Write};

pub use crate::error::{ExecutionError as ESIError, Result};
pub use crate::new_parse::parse;

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

// Process nom parser chunks directly to output - with fragment request support
fn process_nom_chunk_to_output(
    chunk: parser_types::Chunk, 
    ctx: &mut EvalContext,
    output_writer: &mut impl Write,
    original_request_metadata: &Request,
    dispatch_fragment_request: Option<&FragmentRequestDispatcher>,
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
            // Evaluate the expression and write as text
            eprintln!("DEBUG: Evaluating expression: {:?}", expr);
            match evaluate_simple_nom_expr(expr, ctx) {
                Ok(result) => {
                    eprintln!("DEBUG: Expression evaluated to: '{}'", result);
                    if !result.is_empty() {
                        output_writer.write_all(result.as_bytes())?;
                    }
                }
                Err(e) => {
                    eprintln!("DEBUG: Expression evaluation failed: {:?}", e);
                }
            }
            // Swallow errors as intended for expressions
            Ok(())
        }
        Chunk::Esi(tag) => {
            match tag {
                NomTag::Assign { name, value } => {
                    // Handle esi:assign tags - evaluate the value expression and set variable
                    //First, check if the value is a quoted string literal and strip quotes
                    let trimmed = value.trim();
                    let unquoted_value = if trimmed.starts_with('\'') && trimmed.ends_with('\'') && trimmed.len() >= 2 {
                        // Single-quoted string: strip quotes
                        trimmed[1..trimmed.len()-1].to_string()
                    } else if trimmed.starts_with('"') && trimmed.ends_with('"') && trimmed.len() >= 2 {
                        // Double-quoted string: strip quotes
                        trimmed[1..trimmed.len()-1].to_string()
                    } else {
                        value.clone()
                    };
                    
                    // Evaluate the value as an ESI expression
                    let evaluated_value = crate::expression::evaluate_expression(&unquoted_value, ctx)
                        .map(|v| v.to_string())
                        .unwrap_or(unquoted_value);
                    
                    ctx.set_variable(&name, None, crate::expression::Value::Text(evaluated_value.into()));
                    Ok(())
                }
                NomTag::Include { src, alt, continue_on_error } => {
                    if let Some(dispatcher) = dispatch_fragment_request {
                        // Handle esi:include tags - evaluate expressions and build fragment request
                        debug!("Handling <esi:include> tag with src: {}", src);
                        
                        // Always interpolate src
                        let interpolated_src = try_evaluate_interpolated_string(&src, ctx)?;

                        // Build fragment request
                        let req = build_fragment_request(
                            original_request_metadata.clone_without_body(),
                            &interpolated_src,
                            false // assume not escaped for now
                        )?;
                        
                        match dispatcher(req) {
                            Ok(pending_content) => {
                                // Process the fragment content directly
                                match pending_content {
                                    crate::PendingFragmentContent::CompletedRequest(response) => {
                                        // Write the response body directly to output
                                        let body_bytes = response.into_body_bytes();
                                        let body_str = std::str::from_utf8(&body_bytes).unwrap_or("<!-- invalid utf8 -->");
                                        output_writer.write_all(body_str.as_bytes())?;
                                    }
                                    crate::PendingFragmentContent::PendingRequest(_) => {
                                        // For pending requests, just output a placeholder for now
                                        output_writer.write_all(b"<!-- pending request -->")?;
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
                                        let interpolated_alt = try_evaluate_interpolated_string(alt_src, ctx)?;
                                        let alt_req = build_fragment_request(
                                            original_request_metadata.clone_without_body(),
                                            &interpolated_alt,
                                            false
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
                                                output_writer.write_all(b"<!-- fragment request failed -->")?;
                                            }
                                        }
                                    } else {
                                        // No alt, but continue on error
                                        output_writer.write_all(b"<!-- fragment request failed -->")?;
                                    }
                                } else {
                                    return Err(ESIError::ExpressionError(format!("Fragment request failed: {}", err)));
                                }
                            }
                        }
                    } else {
                        // No fragment dispatcher available, output placeholder
                        output_writer.write_all(b"<!-- ESI include not supported -->")?;
                    }
                    Ok(())
                }
                NomTag::Choose { when_branches, otherwise_events } => {
                    // Handle esi:choose/when/otherwise logic - ported from main branch
                    let mut chose_branch = false;
                    for (when_tag, events) in when_branches {
                        if let NomTag::When { test, match_name } = when_tag {
                            if let Some(match_name) = match_name {
                                ctx.set_match_name(&match_name);
                            }
                            let result = crate::expression::evaluate_expression(&test, ctx)?;
                            if result.to_bool() {
                                chose_branch = true;
                                for chunk in events {
                                    process_nom_chunk_to_output(chunk, ctx, output_writer, original_request_metadata, dispatch_fragment_request)?;
                                }
                                break;
                            }
                        }
                    }

                    if !chose_branch {
                        for chunk in otherwise_events {
                            process_nom_chunk_to_output(chunk, ctx, output_writer, original_request_metadata, dispatch_fragment_request)?;
                        }
                    }
                    Ok(())
                }
                NomTag::Vars { name: _ } => {
                    // For now, just output placeholder - this needs to be handled properly
                    output_writer.write_all(b"<!-- ESI vars placeholder -->")?;
                    Ok(())
                }
                _ => {
                    // Handle other tag types as placeholders for now
                    output_writer.write_all(b"<!-- ESI tag not implemented -->")?;
                    Ok(())
                }
            }
        }
    }
}

// Simple nom expression evaluator 
fn evaluate_simple_nom_expr(expr: parser_types::Expr, ctx: &mut EvalContext) -> Result<String> {
    use parser_types::Expr;
    use crate::expression::Value;
    
    match expr {
        Expr::Variable(name, key, _default) => {
            // Evaluate the key expression if present
            let evaluated_key = if let Some(key_expr) = key {
                // Recursively evaluate the key expression
                let key_result = evaluate_simple_nom_expr(*key_expr, ctx)?;
                Some(key_result)
            } else {
                None
            };
            
            let value = ctx.get_variable(name, evaluated_key.as_deref());
            eprintln!("DEBUG: Variable lookup: {}[{:?}] = {:?}", name, evaluated_key, value);
            match value {
                Value::Text(s) => Ok(s.to_string()),
                _ => Ok(String::new()),
            }
        }
        Expr::Call(func_name, args) => {
            // Simple function calls - only handle the basic ones
            match func_name {
                "lower" => {
                    if let Some(arg) = args.first() {
                        let arg_str = evaluate_simple_nom_expr(arg.clone(), ctx)?;
                        Ok(arg_str.to_lowercase())
                    } else {
                        Err(ESIError::FunctionError("lower function requires 1 argument".to_string()))
                    }
                }
                _ => Err(ESIError::FunctionError(format!("Unknown function: {}", func_name)))
            }
        }
        Expr::String(Some(s)) => Ok(s.to_string()),
        Expr::String(None) => Ok(String::new()),
        _ => Ok(String::new()),
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
    /// # Errors
    /// Returns error if:
    /// * ESI markup parsing fails
    /// * Fragment requests fail
    /// * Output writing fails
    pub fn process_document(
        self,
        mut src_document: impl BufRead,
        output_writer: &mut impl Write,
        _dispatch_fragment_request: Option<&FragmentRequestDispatcher>,
        _process_fragment_response: Option<&FragmentResponseProcessor>,
    ) -> Result<()> {

        // If there is a source request to mimic, copy its metadata, otherwise use a default request.
        let original_request_metadata = self.original_request_metadata.as_ref().map_or_else(
            || Request::new(Method::GET, "http://localhost"),
            Request::clone_without_body,
        );

        // Read the entire document into a string for nom parser
        let mut doc_content = String::new();
        src_document.read_to_string(&mut doc_content)
            .map_err(|e| ESIError::WriterError(e))?;

        // Parse the document using nom parser
        let (remaining, chunks) = new_parse::parse(&doc_content)
            .map_err(|e| ESIError::ExpressionError(format!("Nom parser error: {:?}", e)))?;
        
        eprintln!("DEBUG: Parser returned {} chunks", chunks.len());
        for (i, chunk) in chunks.iter().enumerate() {
            eprintln!("DEBUG: Chunk[{}]: {:?}", i, chunk);
        }
        
        // Log warning if parser didn't consume everything (may indicate unsupported features)
        if !remaining.is_empty() {
            debug!("Parser did not consume all input. Remaining: '{}'", 
                   remaining.chars().take(100).collect::<String>());
            eprintln!("DEBUG: Parser remaining: {:?}", remaining);
        }

        // context for the interpreter
        let mut ctx = EvalContext::new();
        ctx.set_request(original_request_metadata.clone_without_body());

        // Process chunks directly to output
        for chunk in chunks {
            process_nom_chunk_to_output(chunk, &mut ctx, output_writer, &original_request_metadata, _dispatch_fragment_request)?;
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

// Simple HTML entity decoder for common entities
fn decode_html_entities(input: &str) -> String {
    input
        .replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&amp;", "&")
        .replace("&quot;", "\"")
        .replace("&apos;", "'")
}

// Helper function to build a fragment request from a URL
// For HTML content the URL is unescaped if it's escaped (default).
// It can be disabled in the processor configuration for a non-HTML content.
fn build_fragment_request(mut request: Request, url: &str, is_escaped: bool) -> Result<Request> {
    let escaped_url = if is_escaped {
        decode_html_entities(url)
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
    let mut buf = vec![];
    let mut cur = input.chars().peekable();

    while let Some(c) = cur.peek() {
        if *c == '$' {
            let mut new_cur = cur.clone();

            if let Some(value) = try_evaluate_interpolated(&mut new_cur, ctx) {
                // If we have accumulated text, output it first
                if !buf.is_empty() {
                    segment_handler(buf.into_iter().collect())?;
                    buf = vec![];
                }

                // Output the evaluated expression result
                segment_handler(value.to_string())?;
            }
            // Update our position
            cur = new_cur;
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
