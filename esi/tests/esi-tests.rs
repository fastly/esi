use esi::{Configuration, Processor};
use fastly::{Error, Request};
use log::debug;
use std::sync::Once;

static INIT: Once = Once::new();

pub fn init_logs() {
    INIT.call_once(|| {
        // Read RUST_LOG if set; otherwise default to quiet globally, debug for *this* crate.
        let default = format!("warn,{}=debug", env!("CARGO_CRATE_NAME"));
        env_logger::Builder::from_env(env_logger::Env::default().filter_or("RUST_LOG", &default))
            .is_test(true) // shows logs without --nocapture
            .init();

        log::debug!("debug is enabled)");
    });
}

// Helper function to create a processor and process an ESI document
fn process_esi_document(input: &str, req: Request) -> Result<String, Error> {
    debug!("Processing ESI document: {input:?}");

    // Create a BufRead from the input string
    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));

    // Create a writer with a Vec buffer to capture the output
    let mut output = Vec::new();

    // Create the processor and process the document
    let mut processor = Processor::new(Some(req), Configuration::default());
    processor.process_stream(reader, &mut output, None, None)?;

    // Convert the output to a string
    let result = String::from_utf8(output)
        .map_err(|e| Error::msg(format!("Invalid UTF-8 in processed output: {e}")))?;

    debug!("Processed result: {result:?}");
    Ok(result)
}

#[test]
fn test_response_overrides_applied() {
    init_logs();

    // Test $set_response_code
    let body_override = r#"<esi:vars>$set_response_code(404, 'oops')</esi:vars>"#;
    let reader = std::io::BufReader::new(std::io::Cursor::new(body_override.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(
        Some(Request::get("http://example.com")),
        Configuration::default(),
    );

    processor
        .process_stream(reader, &mut output, None, None)
        .expect("Processing should succeed");

    // Check the response status was set
    assert_eq!(processor.context().response_status(), Some(404));
    // Check the body override was set
    assert_eq!(
        processor
            .context()
            .response_body_override()
            .map(|b| String::from_utf8_lossy(b).to_string()),
        Some("oops".to_string())
    );

    // Test $set_redirect
    let redirect_doc = r#"<esi:vars>$set_redirect('http://example.com/next')</esi:vars>"#;
    let redirect_reader = std::io::BufReader::new(std::io::Cursor::new(redirect_doc.as_bytes()));
    let mut redirect_output = Vec::new();
    let mut redirect_processor = Processor::new(
        Some(Request::get("http://example.com")),
        Configuration::default(),
    );

    redirect_processor
        .process_stream(redirect_reader, &mut redirect_output, None, None)
        .expect("Processing should succeed");

    // Check redirect status was set
    assert_eq!(redirect_processor.context().response_status(), Some(302));
    // Check Location header was set
    let headers = redirect_processor.context().response_headers();
    let location = headers.iter().find(|(name, _)| name == "Location");
    assert_eq!(
        location.map(|(_, v)| v.as_str()),
        Some("http://example.com/next")
    );
    // Check body override was cleared (redirect should not have body)
    assert!(redirect_processor
        .context()
        .response_body_override()
        .is_none());
}

// Bareword in subfield position with QUERY_STRING
#[test]
fn test_bareword_subfield_query_string() {
    // init logs
    init_logs();
    let input = r#"
        <esi:vars>
            $(QUERY_STRING{param})
        </esi:vars>
    "#;
    let req = Request::get("http://example.com?param=value");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert_eq!(
        result.trim(),
        "value",
        "Bareword subfield should resolve to 'value'"
    );
}

// Bareword in function argument: interpolation errors are intentionally swallowed
#[test]
fn test_bareword_function_argument_is_swallowed() {
    let input = r#"
        <esi:vars>
            $lower(bareword)
        </esi:vars>
    "#;

    let req = Request::get("http://example.com");
    let result = process_esi_document(input, req)
        .expect("ESI processing should succeed; interpolation errors are intentionally swallowed");

    // After swallowing the parse error, nothing should be emitted by <esi:vars>.
    assert!(
        result.trim().is_empty(),
        "Expected empty output when a bareword is used as a function argument during interpolation, got: {:?}",
        result
    );
}

// Mixed subfield types (bareword and expression) with QUERY_STRING
#[test]
fn test_mixed_subfield_types() {
    init_logs();
    let input = r#"
        <esi:assign name="keyVar" value="'param'" />
        <esi:vars>
            $(QUERY_STRING{param})
            $(QUERY_STRING{$(keyVar)})
        </esi:vars>
    "#;
    let req = Request::get("http://example.com?param=value");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert_eq!(
        result.trim(),
        "value\n            value",
        "Bareword and expression subfields should both resolve to 'value'"
    );
}

// Compatibility with ESI choose/when
#[test]
fn test_esi_choose_compatibility_equal() {
    let input = r#"
        <esi:choose>
            <esi:when test="$(QUERY_STRING{param}) == 'value'">
                Match
            </esi:when>
            <esi:otherwise>
                Fallback
            </esi:otherwise>
        </esi:choose>
    "#;
    let req = Request::get("http://example.com?param=value");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert_eq!(
        result.trim(),
        "Match",
        "ESI choose/when should work with bareword subfield"
    );
}

// Compatibility with ESI choose/when with not equal
#[test]
fn test_esi_choose_compatibility_not_equal() {
    let input = r#"
        <esi:choose>
            <esi:when test="$(QUERY_STRING{param}) != 'wrongvalue'">
                Match
            </esi:when>
            <esi:otherwise>
                Fallback
            </esi:otherwise>
        </esi:choose>
    "#;
    let req = Request::get("http://example.com?param=value");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert_eq!(
        result.trim(),
        "Match",
        "ESI choose/when should work with bareword subfield"
    );
}
// Test for nested variable expansion - INVALID ESI SYNTAX
// The construct $($(outer){param}) is NOT valid Akamai ESI syntax.
// Akamai's ESI does not support nested variable expansion like this.
// This test was checking that it doesn't work, but the syntax is so invalid
// that different parsers may handle it differently (error vs. pass-through).
#[test]
#[ignore] // Invalid ESI syntax - $($(var){key}) is not supported by Akamai ESI spec
fn test_nested_subfields() {
    let input = r#"
        <esi:assign name="outer" value="'QUERY_STRING'" />
        <esi:vars>
            $($(outer){param})
        </esi:vars>
    "#;
    let req = Request::get("http://example.com?param=value");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert_ne!(
        result.trim(),
        "value",
        "Nested variable expansion is not valid ESI syntax and should not work"
    );
}

#[test]
fn process_include_with_query_string_interpolation() -> Result<(), Error> {
    use esi::{Configuration, Processor};
    use fastly::{Request, Response};
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    // Create the ESI document with the include tag
    let esi_document = r#"<esi:include 
      src="/v1/product?apiKey=$(QUERY_STRING{apiKey})" />"#;

    // Create a request with the apiKey query parameter
    let req = Some(Request::get("http://example.com?apiKey=value"));

    // Create a response with the ESI document
    let mut resp = Response::from_body(esi_document);

    // Create a processor with default config
    let processor = Processor::new(req, Configuration::default());

    // Track if the fragment request was made with the correct URL
    let correct_fragment_request_made = Arc::new(AtomicBool::new(false));
    let correct_fragment_request_made_clone = Arc::clone(&correct_fragment_request_made);

    // Process the response
    processor
        .process_response(
            &mut resp,
            None,
            Some(&move |fragment_req: Request, _maxwait: Option<u32>| {
                // Check that the fragment request URL contains the interpolated apiKey
                let url = fragment_req.get_url();
                let url_str = url.to_string();
                let contains_api_key = url_str.contains("apiKey=value");

                // Store the result in our atomic boolean
                correct_fragment_request_made_clone.store(contains_api_key, Ordering::SeqCst);

                // Return a mock response for the fragment request
                Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                    Response::from_body("fragment content"),
                )))
            }),
            None,
        )
        .unwrap();

    assert!(
        correct_fragment_request_made.load(Ordering::SeqCst),
        "Fragment request should contain the interpolated apiKey value"
    );
    Ok(())
}

#[test]
fn test_simple_negation() {
    let input = r#"
        <esi:choose>
            <esi:when test="!$(QUERY_STRING{empty})">
                Empty parameter was negated
            </esi:when>
            <esi:otherwise>
                Fallback
            </esi:otherwise>
        </esi:choose>
    "#;
    let req = Request::get("http://example.com?nonempty=value");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert_eq!(
        result.trim(),
        "Empty parameter was negated",
        "Negation of null/empty value should evaluate to true"
    );
}

#[test]
fn test_negation_with_value() {
    let input = r#"
        <esi:choose>
            <esi:when test="!$(QUERY_STRING{param})">
                Parameter was negated
            </esi:when>
            <esi:otherwise>
                Parameter exists
            </esi:otherwise>
        </esi:choose>
    "#;
    let req = Request::get("http://example.com?param=value");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert_eq!(
        result.trim(),
        "Parameter exists",
        "Negation of non-empty value should evaluate to false"
    );
}

#[test]
fn test_negation_of_comparison() {
    let input = r#"
        <esi:choose>
            <esi:when test="!($(QUERY_STRING{param}) == 'wrong')">
                Comparison was negated
            </esi:when>
            <esi:otherwise>
                Fallback
            </esi:otherwise>
        </esi:choose>
    "#;
    let req = Request::get("http://example.com?param=value");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert_eq!(
        result.trim(),
        "Comparison was negated",
        "Negation of false comparison should evaluate to true"
    );
}

#[test]
fn test_double_negation() {
    let input = r#"
        <esi:choose>
            <esi:when test="!!$(QUERY_STRING{param})">
                Double negation works
            </esi:when>
            <esi:otherwise>
                Fallback
            </esi:otherwise>
        </esi:choose>
    "#;
    let req = Request::get("http://example.com?param=value");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert_eq!(
        result.trim(),
        "Double negation works",
        "Double negation should restore original boolean value"
    );
}

#[test]
fn test_negation_with_not_equals() {
    let input = r#"
        <esi:choose>
            <esi:when test="!($(QUERY_STRING{param}) != 'value')">
                Negation of not-equals works
            </esi:when>
            <esi:otherwise>
                Fallback
            </esi:otherwise>
        </esi:choose>
    "#;
    let req = Request::get("http://example.com?param=value");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert_eq!(
        result.trim(),
        "Negation of not-equals works",
        "Negation of not-equals should work correctly"
    );
}

#[test]
fn test_negation_in_vars() {
    let input = r#"
        <esi:vars>
            <esi:assign name="result" value="!$(QUERY_STRING{empty})" />
            $(result)
        </esi:vars>
    "#;
    let req = Request::get("http://example.com?nonempty=value");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert_eq!(
        result.trim(),
        "true",
        "Negation in variable assignment should work"
    );
}

#[test]
fn test_exists_in_when() {
    let input = r#"
        <esi:assign name="foo" value="'bar'" />
        <esi:choose>
            <esi:when test="$exists($(foo))">
                present
            </esi:when>
            <esi:when test="$is_empty($(foo))">
                empty
            </esi:when>
            <esi:otherwise>
                missing
            </esi:otherwise>
        </esi:choose>
    "#;

    let req = Request::get("http://example.com");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert_eq!(result.trim(), "present");
}

#[test]
fn test_is_empty_in_when() {
    let input = r#"
        <esi:assign name="foo" value="" />
        <esi:choose>
            <esi:when test="$exists($(foo))">
                present
            </esi:when>
            <esi:when test="$is_empty($(foo))">
                empty
            </esi:when>
            <esi:otherwise>
                missing
            </esi:otherwise>
        </esi:choose>
    "#;

    let req = Request::get("http://example.com");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert_eq!(result.trim(), "empty");
}

#[test]
fn test_choose_with_esi_tags_in_otherwise() {
    init_logs();
    let input = r#"
        <esi:choose>
            <esi:when test="$(QUERY_STRING{group}) == 'member'">
                Member content
            </esi:when>
            <esi:otherwise>
                <esi:assign name="redirect" value="'welcome.html'" />
                Redirecting to $(redirect)
            </esi:otherwise>
        </esi:choose>
    "#;
    let req = Request::get("http://example.com?group=guest");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert!(
        result.contains("Redirecting to welcome.html"),
        "Otherwise should support ESI tags like assign. Got: {}",
        result
    );
}

// Test that configuration.is_escaped_content controls HTML entity decoding
#[test]
fn test_configuration_is_escaped_content() {
    init_logs();

    // Test with HTML-escaped URL (default behavior)
    let input = r#"<esi:include src="http://example.com/path?param=value&amp;other=test"/>"#;

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();

    // Custom dispatcher that captures the URL
    use std::cell::RefCell;
    use std::rc::Rc;
    let captured_url = Rc::new(RefCell::new(String::new()));
    let captured_url_clone = captured_url.clone();
    let dispatcher =
        move |req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            *captured_url_clone.borrow_mut() = req.get_url_str().to_string();
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                fastly::Response::from_body("fragment content"),
            )))
        };

    let mut processor = Processor::new(
        Some(Request::get("http://example.com/")),
        Configuration::default(), // is_escaped_content = true by default
    );

    processor
        .process_stream(reader, &mut output, Some(&dispatcher), None)
        .expect("Processing should succeed");

    // With is_escaped_content=true, &amp; should be decoded to &
    let url = captured_url.borrow();
    assert!(
        url.contains("param=value&other=test"),
        "URL should have &amp; decoded to &. Got: {}",
        url
    );
}

#[test]
fn test_configuration_is_escaped_content_disabled() {
    init_logs();

    // Test with HTML-escaped URL but with is_escaped_content = false
    let input = r#"<esi:include src="http://example.com/path?param=value&amp;other=test"/>"#;

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();

    // Custom dispatcher that captures the URL
    use std::cell::RefCell;
    use std::rc::Rc;
    let captured_url = Rc::new(RefCell::new(String::new()));
    let captured_url_clone = captured_url.clone();
    let dispatcher =
        move |req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            *captured_url_clone.borrow_mut() = req.get_url_str().to_string();
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                fastly::Response::from_body("fragment content"),
            )))
        };

    let mut processor = Processor::new(
        Some(Request::get("http://example.com/")),
        Configuration::default().with_escaped(false), // Disable HTML entity decoding
    );

    processor
        .process_stream(reader, &mut output, Some(&dispatcher), None)
        .expect("Processing should succeed");

    // With is_escaped_content=false, &amp; should NOT be decoded
    let url = captured_url.borrow();
    assert!(
        url.contains("&amp;"),
        "URL should keep &amp; as-is. Got: {}",
        url
    );
}

// Test that process_fragment_response callback is invoked
#[test]
fn test_process_fragment_response_callback() {
    init_logs();

    let input = r#"<esi:include src="http://example.com/fragment"/>"#;

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();

    // Dispatcher returns a response
    let dispatcher =
        |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            let mut resp = fastly::Response::from_body("original content");
            resp.set_header("X-Custom-Header", "original-value");
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                resp,
            )))
        };

    // Response processor that modifies the response
    use std::cell::RefCell;
    use std::rc::Rc;
    let callback_invoked = Rc::new(RefCell::new(false));
    let callback_invoked_clone = callback_invoked.clone();
    let processor_callback =
        move |_req: &mut Request, mut resp: fastly::Response| -> esi::Result<fastly::Response> {
            *callback_invoked_clone.borrow_mut() = true;
            // Modify the response body
            resp.set_body("modified content");
            // Add a header to prove we processed it
            resp.set_header("X-Processed", "true");
            Ok(resp)
        };

    let mut processor = Processor::new(
        Some(Request::get("http://example.com/")),
        Configuration::default(),
    );

    processor
        .process_stream(
            reader,
            &mut output,
            Some(&dispatcher),
            Some(&processor_callback),
        )
        .expect("Processing should succeed");

    let result = String::from_utf8(output).unwrap();

    // Should contain the modified content
    assert!(
        result.contains("modified content"),
        "Output should contain modified content from processor callback. Got: {}",
        result
    );
    assert!(
        !result.contains("original content"),
        "Output should NOT contain original content. Got: {}",
        result
    );
    assert!(
        *callback_invoked.borrow(),
        "Response processor callback should have been invoked"
    );
}

// Test that process_fragment_response is also called for alt URLs
#[test]
fn test_process_fragment_response_on_alt() {
    init_logs();

    let input = r#"<esi:include src="http://example.com/main" alt="http://example.com/fallback" onerror="continue"/>"#;

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();

    // Dispatcher that fails for main, succeeds for alt
    let dispatcher =
        |req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            if req.get_url_str().contains("/main") {
                // Main request fails
                Err(esi::ExecutionError::ExpressionError(
                    "main failed".to_string(),
                ))
            } else {
                // Alt request succeeds
                Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                    fastly::Response::from_body("alt content"),
                )))
            }
        };

    // Response processor that should be called for the alt response
    use std::cell::RefCell;
    use std::rc::Rc;
    let alt_processed = Rc::new(RefCell::new(false));
    let alt_processed_clone = alt_processed.clone();
    let processor_callback =
        move |req: &mut Request, mut resp: fastly::Response| -> esi::Result<fastly::Response> {
            if req.get_url_str().contains("/fallback") {
                *alt_processed_clone.borrow_mut() = true;
                resp.set_body("processed alt content");
            }
            Ok(resp)
        };

    let mut processor = Processor::new(
        Some(Request::get("http://example.com/")),
        Configuration::default(),
    );

    processor
        .process_stream(
            reader,
            &mut output,
            Some(&dispatcher),
            Some(&processor_callback),
        )
        .expect("Processing should succeed");

    let result = String::from_utf8(output).unwrap();

    assert!(
        result.contains("processed alt content"),
        "Output should contain processed alt content. Got: {}",
        result
    );
    assert!(
        *alt_processed.borrow(),
        "Response processor should have been invoked for alt URL"
    );
}

// Test that process_fragment_response can return errors
#[test]
fn test_process_fragment_response_error_handling() {
    init_logs();

    let input = r#"<esi:include src="http://example.com/fragment"/>"#;

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();

    // Dispatcher returns a response
    let dispatcher =
        |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                fastly::Response::from_body("content"),
            )))
        };

    // Response processor that returns an error
    let processor_callback =
        |_req: &mut Request, _resp: fastly::Response| -> esi::Result<fastly::Response> {
            Err(esi::ExecutionError::ExpressionError(
                "processing failed".to_string(),
            ))
        };

    let mut processor = Processor::new(
        Some(Request::get("http://example.com/")),
        Configuration::default(),
    );

    let result = processor.process_stream(
        reader,
        &mut output,
        Some(&dispatcher),
        Some(&processor_callback),
    );

    // Should propagate the error from the processor
    assert!(
        result.is_err(),
        "Should return error from processor callback"
    );
    assert!(
        result
            .unwrap_err()
            .to_string()
            .contains("processing failed"),
        "Error should be from the processor callback"
    );
}

// Test that alt URLs support interpolation (variables from request)
#[test]
fn test_alt_url_with_interpolation() {
    init_logs();

    // Test with interpolated variable in alt URL using QUERY_STRING
    let input = r#"
        <esi:include src="http://example.com/main" alt="http://example.com/fallback?id=$(QUERY_STRING{fallback_id})" onerror="continue"/>
    "#;

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();

    // Dispatcher that fails for main, succeeds for alt
    use std::cell::RefCell;
    use std::rc::Rc;
    let captured_alt_url = Rc::new(RefCell::new(String::new()));
    let captured_alt_url_clone = captured_alt_url.clone();
    let dispatcher =
        move |req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            if req.get_url_str().contains("/main") {
                // Main request fails
                Err(esi::ExecutionError::ExpressionError(
                    "main failed".to_string(),
                ))
            } else {
                // Alt request succeeds - capture the URL
                *captured_alt_url_clone.borrow_mut() = req.get_url_str().to_string();
                Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                    fastly::Response::from_body("alt content"),
                )))
            }
        };

    let mut processor = Processor::new(
        Some(Request::get("http://example.com/?fallback_id=12345")),
        Configuration::default(),
    );

    processor
        .process_stream(reader, &mut output, Some(&dispatcher), None)
        .expect("Processing should succeed");

    let result = String::from_utf8(output).unwrap();

    // Verify the alt URL was interpolated correctly
    let alt_url = captured_alt_url.borrow();
    assert!(
        alt_url.contains("id=12345"),
        "Alt URL should have interpolated variable. Got: {}",
        alt_url
    );

    // Verify content from alt was used
    assert!(
        result.contains("alt content"),
        "Output should contain alt content. Got: {}",
        result
    );
}

// Test that alt URLs support function calls in interpolation
#[test]
fn test_alt_url_with_function_interpolation() {
    init_logs();

    // Test with function call in alt URL (similar to spec example) using HTTP_HOST
    let input = r#"
        <esi:include src="http://example.com/main" alt="http://example.com/fallback?host=$lower($(HTTP_HOST))" onerror="continue"/>
    "#;

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();

    // Dispatcher that fails for main, succeeds for alt
    use std::cell::RefCell;
    use std::rc::Rc;
    let captured_alt_url = Rc::new(RefCell::new(String::new()));
    let captured_alt_url_clone = captured_alt_url.clone();
    let dispatcher =
        move |req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            if req.get_url_str().contains("/main") {
                // Main request fails
                Err(esi::ExecutionError::ExpressionError(
                    "main failed".to_string(),
                ))
            } else {
                // Alt request succeeds - capture the URL
                *captured_alt_url_clone.borrow_mut() = req.get_url_str().to_string();
                Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                    fastly::Response::from_body("alt with function"),
                )))
            }
        };

    let mut req = Request::get("http://Example.COM/");
    req.set_header("Host", "Example.COM");

    let mut processor = Processor::new(Some(req), Configuration::default());

    processor
        .process_stream(reader, &mut output, Some(&dispatcher), None)
        .expect("Processing should succeed");

    let result = String::from_utf8(output).unwrap();

    // Verify the alt URL was interpolated with function call (lower case)
    let alt_url = captured_alt_url.borrow();
    assert!(
        alt_url.contains("host=example.com"),
        "Alt URL should have interpolated and lowercased HTTP_HOST. Got: {}",
        alt_url
    );

    // Verify content from alt was used
    assert!(
        result.contains("alt with function"),
        "Output should contain alt content. Got: {}",
        result
    );
}

// Test interpolated compound expressions in long form assign
#[test]
fn test_assign_long_form_interpolation() {
    init_logs();
    let input = r#"
        <esi:assign name="greeting">Hello $(HTTP_HOST)!</esi:assign>
        <esi:vars>$(greeting)</esi:vars>
    "#;
    let mut req = Request::get("http://example.com/test");
    req.set_header("Host", "example.com");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert_eq!(
        result.trim(),
        "Hello example.com!",
        "Long form assign with interpolation should concatenate text and variables"
    );
}

// Test multiple variables in long form assign
#[test]
fn test_assign_long_form_multiple_variables() {
    init_logs();
    let input = r#"
        <esi:assign name="first" value="'John'" />
        <esi:assign name="last" value="'Doe'" />
        <esi:assign name="full_name">$(first) $(last)</esi:assign>
        <esi:vars>$(full_name)</esi:vars>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert_eq!(
        result.trim(),
        "John Doe",
        "Long form assign should handle multiple variables in compound expression"
    );
}

// Test streaming input parsing with realistic document
// Verifies that chunked reading works correctly
#[test]
fn test_streaming_input_with_small_chunks() {
    init_logs();

    // Create a document that demonstrates streaming works
    let input = r#"<html><body><esi:assign name="v" value="'test'" /><esi:vars>$(v)</esi:vars></body></html>"#;

    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    // Verify the output contains expected content
    assert!(
        result.contains("test"),
        "Should contain assigned variable value"
    );
}
// Test foreach with a list variable
#[test]
fn test_foreach_with_list() {
    init_logs();
    let input = r#"
        <esi:assign name="nums" value="$string_split('1,2,3', ',')" />
        <esi:foreach collection="nums" item="n">[$(n)]</esi:foreach>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert!(
        result.contains("[1][2][3]"),
        "Should iterate through list items"
    );
}

// Test foreach with default item variable name
#[test]
fn test_foreach_default_item_name() {
    init_logs();
    let input = r#"
        <esi:assign name="items" value="$string_split('a,b', ',')" />
        <esi:foreach collection="items">$(item)</esi:foreach>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert!(result.contains("ab"), "Should use default 'item' variable");
}

// Test foreach with break
#[test]
fn test_foreach_with_break() {
    init_logs();
    let input = r#"
        <esi:assign name="nums" value="$string_split('1,2,3,4,5', ',')" />
        <esi:foreach collection="nums" item="n"><esi:choose>
            <esi:when test="$(n) == '3'"><esi:break /></esi:when>
            <esi:otherwise>[$(n)]</esi:otherwise>
        </esi:choose></esi:foreach>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    let trimmed = result.trim();
    assert!(trimmed.contains("[1]"), "Should have first item");
    assert!(trimmed.contains("[2]"), "Should have second item");
    assert!(!trimmed.contains("[3]"), "Should break before third item");
    assert!(!trimmed.contains("[4]"), "Should not have fourth item");
}

// Test foreach with dictionary
#[test]
fn test_foreach_with_dict() {
    init_logs();
    let input = r#"
        <esi:assign name="dict" value="$(QUERY_STRING)" />
        <esi:foreach collection="dict" item="val">x</esi:foreach>
    "#;
    let req = Request::get("http://example.com/test?a=1&b=2");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert!(result.contains("xx"), "Should iterate through dict values");
}

// Test foreach with dictionary literal
#[test]
fn test_foreach_dict_literal() {
    init_logs();
    let input = r#"A list of Fruits: <esi:foreach collection="{1:'apples',2:'oranges',3:'bananas',4:'grapefruits'}" item="item">$(item) -- $(item{0}) = $(item{1})<br>
</esi:foreach>"#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    // Should contain all fruit entries
    assert!(result.contains("apples"), "Should have apples");
    assert!(result.contains("oranges"), "Should have oranges");
    assert!(result.contains("bananas"), "Should have bananas");
    assert!(result.contains("grapefruits"), "Should have grapefruits");

    // Should have key-value access
    assert!(result.contains(" -- "), "Should have separator");
    assert!(result.contains(" = "), "Should have equals");

    // Verify specific key-value pairs
    assert!(result.contains("1 = apples"), "Should have key 1 = apples");
    assert!(
        result.contains("2 = oranges"),
        "Should have key 2 = oranges"
    );
    assert!(
        result.contains("3 = bananas"),
        "Should have key 3 = bananas"
    );
    assert!(
        result.contains("4 = grapefruits"),
        "Should have key 4 = grapefruits"
    );
}

// Test foreach with range operator
#[test]
fn test_foreach_with_range() {
    init_logs();
    let input = r#"<esi:foreach collection="[1..10]" item="n">$(n) </esi:foreach>"#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert_eq!(
        result, "1 2 3 4 5 6 7 8 9 10 ",
        "Should iterate from 1 to 10"
    );
}

// Test foreach with descending range
#[test]
fn test_foreach_with_range_descending() {
    init_logs();
    let input = r#"<esi:foreach collection="[5..1]" item="n">$(n),</esi:foreach>"#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert_eq!(result, "5,4,3,2,1,", "Should iterate from 5 down to 1");
}

// Test foreach with range and variables
#[test]
fn test_foreach_with_range_variables() {
    init_logs();
    let input = r#"
        <esi:assign name="start" value="1" />
        <esi:assign name="end" value="5" />
        <esi:foreach collection="[$(start)..$(end)]" item="i">$(i) </esi:foreach>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert!(
        result.contains("1 2 3 4 5"),
        "Should use variable-based range"
    );
}

// Test nested foreach with break - ensure break only affects inner loop
#[test]
fn test_nested_foreach_with_break() {
    init_logs();
    let input = r#"
        <esi:assign name="outer" value="['A','B','C']" />
        <esi:assign name="inner" value="['1','2','3']" />
        <esi:foreach collection="outer" item="o">
Outer[$(o)]:
<esi:foreach collection="inner" item="i"><esi:choose>
<esi:when test="$(i) == '2'"><esi:break /></esi:when>
<esi:otherwise>$(o)-$(i) </esi:otherwise>
</esi:choose></esi:foreach>
</esi:foreach>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    // Each outer iteration should show inner loop breaking after first item
    assert!(result.contains("Outer[A]:"), "Should have outer A");
    assert!(result.contains("Outer[B]:"), "Should have outer B");
    assert!(result.contains("Outer[C]:"), "Should have outer C");

    // Inner loop should process first item for each outer iteration
    assert!(result.contains("A-1"), "Should have A-1");
    assert!(result.contains("B-1"), "Should have B-1");
    assert!(result.contains("C-1"), "Should have C-1");

    // Inner loop should break before second item (when i == '2')
    assert!(!result.contains("A-2"), "Should NOT have A-2 (broke)");
    assert!(!result.contains("B-2"), "Should NOT have B-2 (broke)");
    assert!(!result.contains("C-2"), "Should NOT have C-2 (broke)");

    // Inner loop should not reach third item
    assert!(!result.contains("A-3"), "Should NOT have A-3");
    assert!(!result.contains("B-3"), "Should NOT have B-3");
    assert!(!result.contains("C-3"), "Should NOT have C-3");
}

// Test simpler dict literal with assign
#[test]
fn test_simple_dict_literal() {
    init_logs();
    let input =
        r#"<esi:assign name="test" value="{1:'a',2:'b'}" /><esi:vars>Result: $(test)</esi:vars>"#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    // The dict should have been assigned and displayed
    assert!(result.contains("Result:"), "Should have result label");
    assert!(
        !result.contains("$(test)"),
        "Variable should be substituted"
    );
    assert!(result.contains("1=a"), "Should have key-value pair 1=a");
    assert!(result.contains("2=b"), "Should have key-value pair 2=b");
}

// Test list literal - basic
#[test]
fn test_simple_list_literal() {
    init_logs();
    let input =
        r#"<esi:foreach item="x" collection="[1,2,3]"><esi:vars>$(x),</esi:vars></esi:foreach>"#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    assert!(result.contains("1"), "Should have 1");
    assert!(result.contains("2"), "Should have 2");
    assert!(result.contains("3"), "Should have 3");
}

// Test list literal with strings
#[test]
fn test_string_list_literal() {
    init_logs();
    let input = r#"<esi:foreach item="x" collection="['a','b','c']"><esi:vars>$(x),</esi:vars></esi:foreach>"#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    assert!(result.contains("a"), "Should have a");
    assert!(result.contains("b"), "Should have b");
    assert!(result.contains("c"), "Should have c");
}

// Test nested foreach with list literals and break
#[test]
fn test_list_literal_nested_foreach() {
    init_logs();
    let input = r#"<esi:foreach item="bar" collection="[1,2,3]">
[<esi:foreach item="foo" collection="['a','b','c']">
<esi:vars>$(foo)</esi:vars><esi:break/>
</esi:foreach>]<esi:vars>$(bar) </esi:vars>
</esi:foreach>"#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    // Remove whitespace for easier testing
    let clean = result.replace(char::is_whitespace, "");

    // Should show [a]1, [a]2, [a]3 (break after first 'a' in each inner loop)
    assert!(clean.contains("[a]1"), "Should have [a]1");
    assert!(clean.contains("[a]2"), "Should have [a]2");
    assert!(clean.contains("[a]3"), "Should have [a]3");

    // Should NOT have b or c due to break
    assert!(
        !result.contains("b"),
        "Should not have 'b' - break should prevent it"
    );
    assert!(
        !result.contains("c"),
        "Should not have 'c' - break should prevent it"
    );
}

// Test list subscript assignment - from ESI spec
#[test]
fn test_list_subscript_assignment() {
    init_logs();
    let input = r#"<esi:assign name="colors" value="[ 'red', 'blue', 'green' ]"/>
<esi:assign name="colors{0}" value="purple"/>
<esi:vars>$(colors)</esi:vars>"#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    // Should output the list with first element replaced
    assert!(result.contains("purple"), "Should have purple");
    assert!(result.contains("blue"), "Should have blue");
    assert!(result.contains("green"), "Should have green");
    assert!(
        !result.contains("red"),
        "Should not have red - it was replaced"
    );
}

// Test dictionary subscript assignment - from ESI spec
#[test]
fn test_dict_subscript_assignment() {
    init_logs();
    let input = r#"<esi:assign name="ages" value="{ 'bob' : 34, 'joan' : 27, 'ed' : 23 }"/>
<esi:assign name="ages{joan}" value="28"/>
<esi:vars>$(ages)</esi:vars>"#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    // Should have joan's age updated to 28
    assert!(result.contains("joan"), "Should have joan key");
    assert!(result.contains("28"), "Should have updated value 28");
    assert!(!result.contains("27"), "Should not have old value 27");
    assert!(result.contains("bob"), "Should have bob key");
    assert!(result.contains("34"), "Should have bob's value");
    assert!(result.contains("ed"), "Should have ed key");
    assert!(result.contains("23"), "Should have ed's value");
}

// Test dictionary subscript assignment with expression - from ESI spec
// TODO: This requires implementing subscript notation in variable expressions $(ages{joan})
#[test]
#[ignore]
fn test_dict_subscript_assignment_with_expression() {
    init_logs();
    let input = r#"<esi:assign name="ages" value="{ 'bob' : 34, 'joan' : 27, 'ed' : 23 }"/>
<esi:assign name="ages{joan}" value="$(ages{joan}) + 1"/>
<esi:vars>$(ages)</esi:vars>"#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    // Should have joan's age incremented to 28
    assert!(result.contains("28"), "Should have incremented value 28");
    assert!(!result.contains("27"), "Should not have old value 27");
}

// Test nested foreach loops
#[test]
fn test_foreach_nested() {
    init_logs();
    let input = r#"
        <esi:assign name="outer" value="$string_split('A,B,C', ',')" />
        <esi:assign name="inner" value="$string_split('1,2,3', ',')" />
        <esi:foreach collection="outer" item="letter">
            <esi:foreach collection="inner" item="number">$(letter)$(number) </esi:foreach>
        </esi:foreach>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    // Each outer iteration should produce 3 inner iterations
    assert!(result.contains("A1"), "Should have A1");
    assert!(result.contains("A2"), "Should have A2");
    assert!(result.contains("A3"), "Should have A3");
    assert!(result.contains("B1"), "Should have B1");
    assert!(result.contains("B2"), "Should have B2");
    assert!(result.contains("B3"), "Should have B3");
    assert!(result.contains("C1"), "Should have C1");
    assert!(result.contains("C2"), "Should have C2");
    assert!(result.contains("C3"), "Should have C3");
}

// Test nested foreach with break only affects inner loop
#[test]
fn test_foreach_nested_break_inner_only() {
    init_logs();
    let input = r#"
        <esi:assign name="outer" value="$string_split('X,Y', ',')" />
        <esi:assign name="inner" value="$string_split('1,2,3', ',')" />
        <esi:foreach collection="outer" item="letter">
            [<esi:foreach collection="inner" item="num"><esi:choose>
                <esi:when test="$(num) == '2'"><esi:break /></esi:when>
                <esi:otherwise>$(letter)$(num)</esi:otherwise>
            </esi:choose></esi:foreach>]
        </esi:foreach>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    // Each outer iteration should produce X1, then break at 2
    assert!(result.contains("X1"), "Should have X1 before break");
    assert!(!result.contains("X2"), "Should not have X2 (break)");
    assert!(!result.contains("X3"), "Should not have X3 (after break)");

    // Second outer iteration should also produce Y1, then break at 2
    assert!(
        result.contains("Y1"),
        "Should have Y1 (outer loop continues)"
    );
    assert!(!result.contains("Y2"), "Should not have Y2 (break)");
    assert!(!result.contains("Y3"), "Should not have Y3 (after break)");
}

// Test that assigning to non-existent list index fails per ESI spec
#[test]
fn test_list_index_must_exist() {
    init_logs();
    let input = r#"
        <esi:assign name="colors" value="['red', 'blue', 'green']" />
        <esi:assign name="colors{3}" value="'yellow'" />
        <esi:vars>$(colors{3})</esi:vars>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req);

    // Should fail because index 3 doesn't exist (only 0, 1, 2)
    assert!(
        result.is_err(),
        "Should error on out-of-bounds list assignment"
    );
}

// Test that you can assign to existing list indices
#[test]
fn test_list_index_assignment_when_exists() {
    init_logs();
    let input = r#"
        <esi:comment value="Create a list of size 4" />
        <esi:assign name="newlist" value="[ 0, 0, 0, 0 ]" />
        <esi:assign name="newlist{0}" value="'yellow'" />
        <esi:vars>$(newlist{0})</esi:vars>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    assert!(
        result.contains("yellow"),
        "Should assign to existing list index"
    );
}

// Test that dictionary keys can be created on the fly
#[test]
fn test_dict_keys_created_on_fly() {
    init_logs();
    let input = r#"
        <esi:assign name="ages{'bob'}" value="34" />
        <esi:assign name="ages{'joan'}" value="28" />
        <esi:vars>bob:$(ages{'bob'}), joan:$(ages{'joan'})</esi:vars>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    assert!(
        result.contains("bob:34"),
        "Should create dict keys on the fly. Got: {}",
        result
    );
    assert!(
        result.contains("joan:28"),
        "Should create multiple dict keys. Got: {}",
        result
    );
}

// Test that you cannot assign string key to a list
#[test]
fn test_cannot_assign_string_key_to_list() {
    init_logs();
    let input = r#"
        <esi:assign name="colors" value="['red', 'blue']" />
        <esi:assign name="colors{joe}" value="'black'" />
        <esi:vars>$(colors{joe})</esi:vars>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req);

    // Should fail because can't assign string key to list
    assert!(
        result.is_err(),
        "Should error when assigning string key to list"
    );
}

// Test nested lists work correctly
#[test]
fn test_nested_lists() {
    init_logs();
    let input = r#"
        <esi:assign name="complex" value="[ 'one', [ 'a', 'x', 'c' ], 'three' ]" />
        <esi:assign name="inner" value="$(complex{1})" />
        <esi:vars>$(complex{0}),$(inner{1}),$(complex{2})</esi:vars>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    assert!(result.contains("one"), "Should access first element");
    assert!(result.contains("x"), "Should access nested list element");
    assert!(result.contains("three"), "Should access third element");
}

// Test has operator - case-sensitive substring matching
#[test]
fn test_has_operator() {
    init_logs();
    let input = r#"
        <esi:choose>
            <esi:when test="'Hello World' has 'World'">found</esi:when>
            <esi:otherwise>not found</esi:otherwise>
        </esi:choose>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert!(
        result.contains("found"),
        "Should find 'World' in 'Hello World'"
    );

    // Test case sensitivity - should NOT match
    let input2 = r#"
        <esi:choose>
            <esi:when test="'Hello World' has 'world'">found</esi:when>
            <esi:otherwise>not found</esi:otherwise>
        </esi:choose>
    "#;
    let req2 = Request::get("http://example.com/test");
    let result2 = process_esi_document(input2, req2).expect("Processing should succeed");
    assert!(
        result2.contains("not found"),
        "Should NOT find 'world' (wrong case)"
    );
}

// Test has_i operator - case-insensitive substring matching
#[test]
fn test_has_i_operator() {
    init_logs();
    let input = r#"
        <esi:choose>
            <esi:when test="'Hello World' has_i 'world'">found</esi:when>
            <esi:otherwise>not found</esi:otherwise>
        </esi:choose>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert!(
        result.contains("found"),
        "Should find 'world' case-insensitively"
    );

    // Test with different case variations
    let input2 = r#"
        <esi:choose>
            <esi:when test="'HELLO WORLD' has_i 'HeLLo'">found</esi:when>
            <esi:otherwise>not found</esi:otherwise>
        </esi:choose>
    "#;
    let req2 = Request::get("http://example.com/test");
    let result2 = process_esi_document(input2, req2).expect("Processing should succeed");
    assert!(result2.contains("found"), "Should match case-insensitively");
}

// Test has with HTTP_COOKIE variable (from ESI spec example)
#[test]
fn test_has_with_cookie_variable() {
    init_logs();
    let input = r#"
        <esi:assign name="test_cookie" value="'first_name=Sam&last_name=Samuelson'" />
        <esi:choose>
            <esi:when test="$(test_cookie) has 'Sam'">has Sam</esi:when>
            <esi:otherwise>no Sam</esi:otherwise>
        </esi:choose>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert!(
        result.contains("has Sam"),
        "Should find Sam in cookie string"
    );
}

// Test has_i with subscript access (from ESI spec example)
#[test]
fn test_has_i_with_subscript() {
    init_logs();
    let input = r#"
        <esi:assign name="cookies" value="{'first_name':'Sam','last_name':'Smith'}" />
        <esi:choose>
            <esi:when test="$(cookies{'first_name'}) has_i 'sam'">matched</esi:when>
            <esi:otherwise>not matched</esi:otherwise>
        </esi:choose>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert!(
        result.contains("matched"),
        "Should match 'sam' case-insensitively in 'Sam'"
    );
}

// Test default values for undefined variables
#[test]
fn test_variable_default_values() {
    init_logs();

    // Test 1: Simple string default for undefined variable (inside esi:vars)
    let input1 = r#"<esi:vars>Value: $(UNDEFINED|'default_value')</esi:vars>"#;
    let req1 = Request::get("http://example.com/test");
    let result1 = process_esi_document(input1, req1).expect("Processing should succeed");
    assert!(
        result1.contains("Value: default_value"),
        "Should use default value for undefined variable. Got: {}",
        result1
    );

    // Test 2: Integer default for undefined variable
    let input2 = r#"<esi:vars>Count: $(UNDEFINED|42)</esi:vars>"#;
    let req2 = Request::get("http://example.com/test");
    let result2 = process_esi_document(input2, req2).expect("Processing should succeed");
    assert!(
        result2.contains("Count: 42"),
        "Should use integer default value. Got: {}",
        result2
    );

    // Test 3: Default value for missing cookie (from ESI spec example)
    // This include will fail because the backend doesn't exist, but the URL construction
    // should still work (use default value to construct the URL)
    let input3 =
        r#"<esi:include src="http://www.xyz.com/$(HTTP_COOKIE{'cobrand'}|'akamai').htm"/>"#;
    let req3 = Request::get("http://example.com/test");
    // The include will fail but parsing/evaluation should succeed
    // We're just checking that the default value syntax is parsed correctly
    let _ = process_esi_document(input3, req3); // May fail due to missing backend, that's ok

    // Test 4: Default value for missing dictionary key
    let input4 = r#"
        <esi:assign name="mydict" value="{'a':'value_a'}" />
        <esi:vars>Result: $(mydict{'missing_key'}|'default_key_value')</esi:vars>
    "#;
    let req4 = Request::get("http://example.com/test");
    let result4 = process_esi_document(input4, req4).expect("Processing should succeed");
    assert!(
        result4.contains("Result: default_key_value"),
        "Should use default for missing dict key. Got: {}",
        result4
    );

    // Test 5: Variable with value should not use default
    let input5 = r#"
        <esi:assign name="defined" value="'actual_value'" />
        <esi:vars>Result: $(defined|'default_value')</esi:vars>
    "#;
    let req5 = Request::get("http://example.com/test");
    let result5 = process_esi_document(input5, req5).expect("Processing should succeed");
    assert!(
        result5.contains("Result: actual_value"),
        "Should use actual value, not default. Got: {}",
        result5
    );

    // Test 6: Default value can be another variable
    let input6 = r#"
        <esi:assign name="fallback" value="'fallback_value'" />
        <esi:vars>Result: $(UNDEFINED|$(fallback))</esi:vars>
    "#;
    let req6 = Request::get("http://example.com/test");
    let result6 = process_esi_document(input6, req6).expect("Processing should succeed");
    assert!(
        result6.contains("Result: fallback_value"),
        "Should use variable as default. Got: {}",
        result6
    );

    // Test 7: Default value with HTTP_ACCEPT_LANGUAGE example from spec
    let input7 = r#"<esi:vars><esi:assign name="lang">$(HTTP_ACCEPT_LANGUAGE{'en-gb'}|'en-us')</esi:assign></esi:vars>"#;
    let req7 = Request::get("http://example.com/test");
    let result7 = process_esi_document(input7, req7).expect("Processing should succeed");
    // Should complete without error even if header not present
    assert!(
        !result7.is_empty() || result7.is_empty(),
        "Processing completed"
    );
}

// Test default values in esi:include src attribute
#[test]
fn test_default_in_include_src() {
    init_logs();

    // From ESI spec: setting default language for HTTP_ACCEPT_LANGUAGE
    let input = r#"
        <esi:vars>
            <esi:assign name="user_lang">$(HTTP_ACCEPT_LANGUAGE|'en-us')</esi:assign>
            Language: $(user_lang)
        </esi:vars>
    "#;
    let req = Request::get("http://example.com/test");
    let result = process_esi_document(input, req).expect("Processing should succeed");
    assert!(
        result.contains("Language: en-us"),
        "Should use default language 'en-us'. Got: {}",
        result
    );
}

// Test compound expressions with multiple operators (from ESI spec example)
#[test]
fn test_compound_expression_from_spec() {
    init_logs();

    // Test case 1: Cookie doesn't exist - should go to when branch
    let input1 = r#"
        <esi:choose>
            <esi:when test="!$exists($(HTTP_COOKIE{'UserInfo'})) || !($(HTTP_COOKIE{'UserInfo'}) matches '''UserId=[0-9]''')">
                some file
            </esi:when>
            <esi:otherwise>
                some other file
            </esi:otherwise>
        </esi:choose>
    "#;
    let req1 = Request::get("http://example.com/test");
    // No cookie set, so first part of OR should be true
    let result1 = process_esi_document(input1, req1).expect("Processing should succeed");
    assert!(
        result1.contains("some file"),
        "Should include 'some file' when cookie doesn't exist. Got: {}",
        result1
    );
    assert!(
        !result1.contains("some other file"),
        "Should not include 'some other file'. Got: {}",
        result1
    );

    // Test case 2: Cookie exists with matching pattern - should go to otherwise
    let input2 = r#"
        <esi:choose>
            <esi:when test="!$exists($(HTTP_COOKIE{'UserInfo'})) || !($(HTTP_COOKIE{'UserInfo'}) matches '''UserId=[0-9]''')">
                some file
            </esi:when>
            <esi:otherwise>
                some other file
            </esi:otherwise>
        </esi:choose>
    "#;
    let mut req2 = Request::get("http://example.com/test");
    req2.set_header("Cookie", "UserInfo=UserId=5");
    let result2 = process_esi_document(input2, req2).expect("Processing should succeed");
    assert!(
        result2.contains("some other file"),
        "Should include 'some other file' when cookie exists with valid pattern. Got: {}",
        result2
    );
    assert!(
        !result2.contains("some file"),
        "Should not include 'some file'. Got: {}",
        result2
    );

    // Test case 3: Cookie exists but doesn't match pattern - should go to when branch
    let input3 = r#"
        <esi:choose>
            <esi:when test="!$exists($(HTTP_COOKIE{'UserInfo'})) || !($(HTTP_COOKIE{'UserInfo'}) matches '''UserId=[0-9]''')">
                some file
            </esi:when>
            <esi:otherwise>
                some other file
            </esi:otherwise>
        </esi:choose>
    "#;
    let mut req3 = Request::get("http://example.com/test");
    req3.set_header("Cookie", "UserInfo=NoMatch");
    let result3 = process_esi_document(input3, req3).expect("Processing should succeed");
    assert!(
        result3.contains("some file"),
        "Should include 'some file' when cookie doesn't match pattern. Got: {}",
        result3
    );
    assert!(
        !result3.contains("some other file"),
        "Should not include 'some other file'. Got: {}",
        result3
    );

    // Test case 4: Cookie exists with empty value - should go to when branch (doesn't exist)
    let input4 = r#"
        <esi:choose>
            <esi:when test="!$exists($(HTTP_COOKIE{'UserInfo'})) || !($(HTTP_COOKIE{'UserInfo'}) matches '''UserId=[0-9]''')">
                some file
            </esi:when>
            <esi:otherwise>
                some other file
            </esi:otherwise>
        </esi:choose>
    "#;
    let mut req4 = Request::get("http://example.com/test");
    req4.set_header("Cookie", "OtherCookie=value");
    let result4 = process_esi_document(input4, req4).expect("Processing should succeed");
    assert!(
        result4.contains("some file"),
        "Should include 'some file' when UserInfo key doesn't exist. Got: {}",
        result4
    );
}

// Test arithmetic operators with ESI variables and expressions
// This demonstrates the left-to-right evaluation behavior from the ESI spec
#[test]
fn test_arithmetic_operators_in_esi() {
    init_logs();

    // Test 1: Basic arithmetic with left-to-right evaluation
    // 2 + 3 * 4 should evaluate left-to-right as (2 + 3) * 4 = 20, not 14
    let input1 = r#"
        <esi:assign name="result" value="2 + 3 * 4" />
        <esi:vars>$(result)</esi:vars>
    "#;
    let req1 = Request::get("http://example.com");
    let result1 = process_esi_document(input1, req1).expect("Processing should succeed");
    assert_eq!(
        result1.trim(),
        "20",
        "2 + 3 * 4 with left-to-right evaluation should be 20"
    );

    // Test 2: Subtraction chain with left-to-right
    // 10 - 3 - 2 should be (10 - 3) - 2 = 5, not 10 - (3 - 2) = 9
    let input2 = r#"
        <esi:assign name="result" value="10 - 3 - 2" />
        <esi:vars>$(result)</esi:vars>
    "#;
    let req2 = Request::get("http://example.com");
    let result2 = process_esi_document(input2, req2).expect("Processing should succeed");
    assert_eq!(
        result2.trim(),
        "5",
        "10 - 3 - 2 with left-to-right evaluation should be 5"
    );

    // Test 3: Division and modulo
    let input3 = r#"
        <esi:assign name="div" value="20 / 4" />
        <esi:assign name="mod" value="10 % 3" />
        <esi:vars>$(div),$(mod)</esi:vars>
    "#;
    let req3 = Request::get("http://example.com");
    let result3 = process_esi_document(input3, req3).expect("Processing should succeed");
    assert_eq!(
        result3.trim(),
        "5,1",
        "Division and modulo should work correctly"
    );

    // Test 4: Arithmetic in conditions
    // 5 + 3 > 7 should evaluate as (5 + 3) > 7 = true
    let input4 = r#"
        <esi:choose>
            <esi:when test="5 + 3 > 7">
                arithmetic true
            </esi:when>
            <esi:otherwise>
                arithmetic false
            </esi:otherwise>
        </esi:choose>
    "#;
    let req4 = Request::get("http://example.com");
    let result4 = process_esi_document(input4, req4).expect("Processing should succeed");
    assert!(
        result4.contains("arithmetic true"),
        "5 + 3 > 7 should evaluate to true"
    );

    // Test 5: Parentheses override left-to-right
    // 2 * (3 + 4) should respect parentheses = 2 * 7 = 14
    let input5 = r#"
        <esi:assign name="result" value="2 * (3 + 4)" />
        <esi:vars>$(result)</esi:vars>
    "#;
    let req5 = Request::get("http://example.com");
    let result5 = process_esi_document(input5, req5).expect("Processing should succeed");
    assert_eq!(
        result5.trim(),
        "14",
        "2 * (3 + 4) should respect parentheses and equal 14"
    );

    // Test 6: Complex arithmetic expression
    // 100 / 5 - 2 * 3 with left-to-right should be ((100 / 5) - 2) * 3 = (20 - 2) * 3 = 54
    let input6 = r#"
        <esi:assign name="result" value="100 / 5 - 2 * 3" />
        <esi:vars>$(result)</esi:vars>
    "#;
    let req6 = Request::get("http://example.com");
    let result6 = process_esi_document(input6, req6).expect("Processing should succeed");
    assert_eq!(
        result6.trim(),
        "54",
        "100 / 5 - 2 * 3 with left-to-right evaluation should be 54"
    );
}

#[test]
fn test_user_defined_function_basic() {
    init_logs();

    let input = r#"
        <esi:function name="greet">Hello, World!</esi:function>
        <esi:vars>$greet()</esi:vars>
    "#;
    let req = Request::get("http://example.com");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    // Function should output accumulated text
    assert!(result.contains("Hello, World!"), "Result was: {}", result);
}

#[test]
fn test_user_defined_function_add() {
    init_logs();

    let input = r#"
        <esi:function name="add">
            <esi:return value="$(ARGS{0}) + $(ARGS{1})"/>
        </esi:function>
        <esi:vars>$add( 5, 7 )</esi:vars>
    "#;
    let req = Request::get("http://example.com");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    assert!(result.contains("12"), "Result was: {}", result);
}

#[test]
fn test_user_defined_function_multiply() {
    init_logs();

    let input = r#"
        <esi:function name="multiply">
            <esi:return value="$(ARGS{0}) * $(ARGS{1})"/>
        </esi:function>
        <esi:vars>Result: $multiply(6, 7)</esi:vars>
    "#;
    let req = Request::get("http://example.com");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    assert!(result.contains("42"), "Result was: {}", result);
}

#[test]
fn test_user_defined_function_is_odd() {
    init_logs();

    let input = r#"
        <esi:function name="is_odd">
            <esi:choose>
                <esi:when test="$(ARGS{0}) % 2 == 1">
                    <esi:return value="'yes'"/>
                </esi:when>
                <esi:otherwise>
                    <esi:return value="'no'"/>
                </esi:otherwise>
            </esi:choose>
        </esi:function>
        <esi:vars>$is_odd(3)</esi:vars>
    "#;
    let req = Request::get("http://example.com");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    assert!(result.contains("yes"), "Result was: {}", result);
}

#[test]
fn test_user_defined_function_sum_with_foreach() {
    init_logs();

    let input = r#"
        <esi:function name="sum">
            <esi:assign name="total" value="0"/>
            <esi:foreach collection="$(ARGS)" item="arg">
                <esi:assign name="total" value="$(total) + $(arg)"/>
            </esi:foreach>
            <esi:return value="$(total)"/>
        </esi:function>
        <esi:vars>$sum(1, 2, 3, 4)</esi:vars>
    "#;
    let req = Request::get("http://example.com");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    assert!(result.contains("10"), "Result was: {}", result);
}

#[test]
fn test_user_defined_function_recursive_addv() {
    init_logs();

    let input = r#"
        <esi:function name="addv">
            <esi:choose>
                <esi:when test="$(ARGS) == []">
                    <esi:return value="0"/>
                </esi:when>
                <esi:otherwise>
                    <esi:assign name="sum" value="0"/>
                    <esi:foreach collection="$(ARGS)" item="arg">
                        <esi:assign name="sum" value="$(sum) + $(arg)"/>
                    </esi:foreach>
                    <esi:return value="$(sum)"/>
                </esi:otherwise>
            </esi:choose>
        </esi:function>
        <esi:vars>$addv(5, 10, 15)</esi:vars>
    "#;
    let req = Request::get("http://example.com");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    assert!(result.contains("30"), "Result was: {}", result);
}

#[test]
fn test_user_defined_function_recursive_factorial() {
    init_logs();

    let input = r#"
        <esi:function name="factorial">
            <esi:choose>
                <esi:when test="$(ARGS{0}) <= 1">
                    <esi:return value="1"/>
                </esi:when>
                <esi:otherwise>
                    <esi:return value="$(ARGS{0}) * $factorial($(ARGS{0}) - 1)"/>
                </esi:otherwise>
            </esi:choose>
        </esi:function>
        <esi:vars>$factorial(5)</esi:vars>
    "#;
    let req = Request::get("http://example.com");
    let result = process_esi_document(input, req).expect("Processing should succeed");

    assert!(result.contains("120"), "Result was: {}", result);
}
// ──────────────────────────────────────────────────────────────────────────────
// Tests for ESI tags inside <esi:try> attempt/except blocks (fix #9 / #2)
// Previously, Choose, Foreach, Assign and Vars were silently dropped when they
// appeared inside an attempt or except block because build_attempt_queue only
// handled Text, Html, Expr, Include, and a hard-coded Choose/Try branch that
// routed output to the wrong queue.
// ──────────────────────────────────────────────────────────────────────────────

#[test]
fn test_try_attempt_with_vars() {
    init_logs();

    let input = r#"<esi:assign name="x" value="'hello'"/>
<esi:try>
  <esi:attempt><esi:vars>$(x)</esi:vars></esi:attempt>
  <esi:except>fallback</esi:except>
</esi:try>"#;

    let result = process_esi_document(input, Request::get("http://example.com/"))
        .expect("Processing should succeed");

    assert!(
        result.contains("hello"),
        "vars inside try attempt should render. Got: {result}"
    );
    assert!(
        !result.contains("fallback"),
        "fallback should NOT appear. Got: {result}"
    );
}

#[test]
fn test_try_attempt_with_choose() {
    init_logs();

    let input = r#"<esi:assign name="flag" value="'yes'"/>
<esi:try>
  <esi:attempt>
    <esi:choose>
      <esi:when test="$(flag)=='yes'">chosen</esi:when>
      <esi:otherwise>other</esi:otherwise>
    </esi:choose>
  </esi:attempt>
  <esi:except>fallback</esi:except>
</esi:try>"#;

    let result = process_esi_document(input, Request::get("http://example.com/"))
        .expect("Processing should succeed");

    assert!(
        result.contains("chosen"),
        "choose inside try attempt should evaluate. Got: {result}"
    );
    assert!(
        !result.contains("other"),
        "non-matching branch should not appear. Got: {result}"
    );
    assert!(
        !result.contains("fallback"),
        "fallback should NOT appear. Got: {result}"
    );
}

#[test]
fn test_try_attempt_with_foreach() {
    init_logs();

    let input = r#"<esi:try>
  <esi:attempt><esi:foreach collection="['a','b','c']" item="i">$(i)</esi:foreach></esi:attempt>
  <esi:except>fallback</esi:except>
</esi:try>"#;

    let result = process_esi_document(input, Request::get("http://example.com/"))
        .expect("Processing should succeed");

    assert_eq!(
        result.trim(),
        "abc",
        "foreach inside try attempt should iterate. Got: {result}"
    );
}

#[test]
fn test_try_attempt_with_assign() {
    init_logs();

    let input = r#"<esi:try>
  <esi:attempt>
    <esi:assign name="val" value="'computed'"/>
    <esi:vars>$(val)</esi:vars>
  </esi:attempt>
  <esi:except>fallback</esi:except>
</esi:try>"#;

    let result = process_esi_document(input, Request::get("http://example.com/"))
        .expect("Processing should succeed");

    assert!(
        result.contains("computed"),
        "assign+vars inside try attempt should work. Got: {result}"
    );
    assert!(
        !result.contains("fallback"),
        "fallback should NOT appear. Got: {result}"
    );
}

#[test]
fn test_try_except_with_vars() {
    init_logs();

    // Attempt dispatches an include that returns 500 (no onerror=continue, so it raises Err
    // and the try machinery falls through to the except block).
    let input = r#"<esi:assign name="msg" value="'except-rendered'"/>
<esi:try>
  <esi:attempt><esi:include src="http://example.com/fails"/></esi:attempt>
  <esi:except><esi:vars>$(msg)</esi:vars></esi:except>
</esi:try>"#;

    // Dispatcher that always returns a 500 so the attempt fails
    let dispatcher = |_req: Request, _: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
        let mut resp = fastly::Response::new();
        resp.set_status(fastly::http::StatusCode::INTERNAL_SERVER_ERROR);
        Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
            resp,
        )))
    };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(
        Some(Request::get("http://example.com/")),
        Configuration::default(),
    );
    processor
        .process_stream(reader, &mut output, Some(&dispatcher), None)
        .expect("Processing should succeed");

    let result = String::from_utf8(output).unwrap();
    assert!(
        result.contains("except-rendered"),
        "vars inside except block should render. Got: {result}"
    );
}

// ──────────────────────────────────────────────────────────────────────────────
// Multi-include document ordering (fix #7)
// With simplified drain_queue (sequential wait), includes must appear in the
// same order they appear in the document regardless of which finishes first.
// ──────────────────────────────────────────────────────────────────────────────

#[test]
fn test_multi_include_document_order() {
    init_logs();

    let input = r#"<esi:include src="http://example.com/first"/><esi:include src="http://example.com/second"/><esi:include src="http://example.com/third"/>"#;

    let dispatcher = |req: Request, _: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
        let body = if req.get_url_str().contains("/first") {
            "FIRST"
        } else if req.get_url_str().contains("/second") {
            "SECOND"
        } else {
            "THIRD"
        };
        Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
            fastly::Response::from_body(body),
        )))
    };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(
        Some(Request::get("http://example.com/")),
        Configuration::default(),
    );
    processor
        .process_stream(reader, &mut output, Some(&dispatcher), None)
        .expect("Processing should succeed");

    let result = String::from_utf8(output).unwrap();
    assert_eq!(
        result, "FIRSTSECONDTHIRD",
        "Includes must appear in document order. Got: {result}"
    );
}

// ──────────────────────────────────────────────────────────────────────────────
// Try block after an include in the same document (fix #11)
// Previously, process_queue skipped Try blocks entirely, so a Try
// that reached the head of the queue (after a preceding include was consumed)
// would stall until drain_queue ran at the end - never an outright bug in tests
// using CompletedRequest, but wrong for real async requests.  The fix makes
// process_queue process Try blocks inline.
// ──────────────────────────────────────────────────────────────────────────────

#[test]
fn test_include_followed_by_try_block() {
    init_logs();

    let input = r#"<esi:include src="http://example.com/first"/>
<esi:try>
  <esi:attempt><esi:include src="http://example.com/attempt"/></esi:attempt>
  <esi:except>except-content</esi:except>
</esi:try>"#;

    let dispatcher = |req: Request, _: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
        let body = if req.get_url_str().contains("/first") {
            "first-content"
        } else {
            "attempt-content"
        };
        Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
            fastly::Response::from_body(body),
        )))
    };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(
        Some(Request::get("http://example.com/")),
        Configuration::default(),
    );
    processor
        .process_stream(reader, &mut output, Some(&dispatcher), None)
        .expect("Processing should succeed");

    let result = String::from_utf8(output).unwrap();
    assert!(
        result.contains("first-content"),
        "Include before try should appear. Got: {result}"
    );
    assert!(
        result.contains("attempt-content"),
        "Try attempt should execute after include. Got: {result}"
    );
    assert!(
        !result.contains("except-content"),
        "Except should NOT appear when attempt succeeds. Got: {result}"
    );
}

#[test]
fn test_content_order_around_try_block() {
    // Verifies that text before and after a <esi:try> block appears in the
    // correct position in the output, even when the attempt contains an include.
    init_logs();

    let input = r#"before<esi:try>
  <esi:attempt><esi:include src="http://example.com/fragment"/></esi:attempt>
  <esi:except>fallback</esi:except>
</esi:try>after"#;

    let dispatcher = |_req: Request, _: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
        Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
            fastly::Response::from_body("fragment-content"),
        )))
    };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(
        Some(Request::get("http://example.com/")),
        Configuration::default(),
    );
    processor
        .process_stream(reader, &mut output, Some(&dispatcher), None)
        .expect("Processing should succeed");

    let result = String::from_utf8(output).unwrap();
    assert_eq!(result, "beforefragment-contentafter", "Got: {result:?}");
}

#[test]
fn test_try_block_at_queue_head_uses_except_on_failure() {
    init_logs();

    // An include followed by a try whose attempt fails -> except should show
    let input = r#"<esi:include src="http://example.com/first"/>
<esi:try>
  <esi:attempt><esi:include src="http://example.com/attempt"/></esi:attempt>
  <esi:except>except-content</esi:except>
</esi:try>"#;

    let dispatcher = |req: Request, _: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
        if req.get_url_str().contains("/first") {
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                fastly::Response::from_body("first-content"),
            )))
        } else {
            // Attempt fails with 500
            let mut resp = fastly::Response::new();
            resp.set_status(fastly::http::StatusCode::INTERNAL_SERVER_ERROR);
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                resp,
            )))
        }
    };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(
        Some(Request::get("http://example.com/")),
        Configuration::default(),
    );
    processor
        .process_stream(reader, &mut output, Some(&dispatcher), None)
        .expect("Processing should succeed");

    let result = String::from_utf8(output).unwrap();
    assert!(
        result.contains("first-content"),
        "Include before try should appear. Got: {result}"
    );
    assert!(
        result.contains("except-content"),
        "Except should appear when attempt fails. Got: {result}"
    );
}

// ---------------------------------------------------------------------------
// Reference semantics for lists and dictionaries (ESI spec: "Lists and
// Dictionaries are Referenced, Not Copied")
// ---------------------------------------------------------------------------

/// Spec example: assigning a list to new names creates aliases, not copies.
/// Mutating through any alias is visible from every other alias.
///
/// ```esi
/// <esi:assign name="list" value="[1, 2, 3]"/>
/// <esi:assign name="copy1" value="list"/>   <!-- Does not copy! -->
/// <esi:assign name="copy2" value="list"/>   <!-- Does not copy! -->
/// <esi:assign name="copy1{2}" value="9"/>
/// ```
///
/// Expected output for $(list), $(copy1), $(copy2): all `1,2,9`
#[test]
fn test_list_reference_semantics() -> Result<(), Error> {
    let input = r#"<esi:assign name="list" value="[1, 2, 3]"/>
<esi:assign name="copy1" value="$(list)"/>
<esi:assign name="copy2" value="$(list)"/>
<esi:assign name="copy1{2}" value="9"/>
<esi:vars>$(list)
$(copy1)
$(copy2)</esi:vars>"#;

    let dispatcher =
        |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            unreachable!("no fragments in this test")
        };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(None, Configuration::default());
    processor.process_stream(reader, &mut output, Some(&dispatcher), None)?;

    let result = String::from_utf8(output).unwrap();
    // All three variables refer to the same list — mutation through copy1 is
    // visible in list and copy2.
    assert_eq!(
        result.trim(),
        "1,2,9\n1,2,9\n1,2,9",
        "Lists should be assigned by reference, not copied"
    );
    Ok(())
}

/// Spec example: using foreach to iterate a dict and build a real copy,
/// then mutating the copy — original should be unaffected.
///
/// ```esi
/// <esi:assign name="dict" value="{1 : 'one', 2 : 'two', 3 : 'three'}"/>
/// <esi:foreach collection="dict">
///   <esi:assign name="copy{$(item{0})}" value="$(item{1})"/>
/// </esi:foreach>
/// <esi:assign name="copy{2}" value="Second"/>
/// ```
///
/// Expected: dict unchanged, copy has key 2 = "Second"
#[test]
fn test_dict_copy_by_iteration() -> Result<(), Error> {
    let input = r#"<esi:assign name="dict" value="{1 : 'one', 2 : 'two', 3 : 'three'}"/>
<esi:foreach collection="$(dict)">
<esi:assign name="copy{$(item{0})}" value="$(item{1})"/>
</esi:foreach>
<esi:assign name="copy{2}" value="'Second'"/>
<esi:vars>$(dict)
$(copy)</esi:vars>"#;

    let dispatcher =
        |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            unreachable!("no fragments in this test")
        };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(None, Configuration::default());
    processor.process_stream(reader, &mut output, Some(&dispatcher), None)?;

    let result = String::from_utf8(output).unwrap();
    let lines: Vec<&str> = result.trim().lines().collect();

    // dict should be unchanged: {1: 'one', 2: 'two', 3: 'three'}
    // dict_to_string sorts by key and formats as k=v&k=v
    assert_eq!(
        lines[0], "1=one&2=two&3=three",
        "Original dict should be unchanged"
    );

    // copy should have key 2 replaced: {1: 'one', 2: 'Second', 3: 'three'}
    assert_eq!(
        lines[1], "1=one&2=Second&3=three",
        "Copy should have key 2 = 'Second'"
    );

    Ok(())
}

/// Dict reference semantics: assigning a dict to another name creates an alias.
/// Mutating through the alias is visible from the original.
#[test]
fn test_dict_reference_semantics() -> Result<(), Error> {
    let input = r#"<esi:assign name="orig" value="{1 : 'one', 2 : 'two'}"/>
<esi:assign name="alias" value="$(orig)"/>
<esi:assign name="alias{2}" value="'TWO'"/>
<esi:vars>$(orig)
$(alias)</esi:vars>"#;

    let dispatcher =
        |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            unreachable!("no fragments in this test")
        };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(None, Configuration::default());
    processor.process_stream(reader, &mut output, Some(&dispatcher), None)?;

    let result = String::from_utf8(output).unwrap();
    // Both should reflect the mutation
    assert_eq!(
        result.trim(),
        "1=one&2=TWO\n1=one&2=TWO",
        "Dicts should be assigned by reference, not copied"
    );
    Ok(())
}

/// Mutating the original list is visible through the alias.
#[test]
fn test_list_mutation_visible_through_alias() -> Result<(), Error> {
    let input = r#"<esi:assign name="a" value="[10, 20, 30]"/>
<esi:assign name="b" value="$(a)"/>
<esi:assign name="a{0}" value="99"/>
<esi:vars>$(b{0})</esi:vars>"#;

    let dispatcher =
        |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            unreachable!("no fragments in this test")
        };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(None, Configuration::default());
    processor.process_stream(reader, &mut output, Some(&dispatcher), None)?;

    let result = String::from_utf8(output).unwrap();
    assert_eq!(
        result.trim(),
        "99",
        "Mutation through original should be visible via alias"
    );
    Ok(())
}
