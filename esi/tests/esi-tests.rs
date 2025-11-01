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
    let processor = Processor::new(Some(req), Configuration::default());
    processor.process_document(reader, &mut output, None, None)?;

    // Convert the output to a string
    let result = String::from_utf8(output)
        .map_err(|e| Error::msg(format!("Invalid UTF-8 in processed output: {e}")))?;

    debug!("Processed result: {result:?}");
    Ok(result)
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
// Test for nested subfields
#[test]
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
        "Nested variable resolution should not work"
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
            Some(&move |fragment_req: Request| {
                // Check that the fragment request URL contains the interpolated apiKey
                let url = fragment_req.get_url();
                let contains_api_key = url.to_string().contains("apiKey=value");

                // Store the result in our atomic boolean
                correct_fragment_request_made_clone.store(contains_api_key, Ordering::SeqCst);

                // Return a mock response for the fragment request
                Ok(esi::PendingFragmentContent::CompletedRequest(
                    Response::from_body("fragment content"),
                ))
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
    let dispatcher = move |req: Request| -> esi::Result<esi::PendingFragmentContent> {
        *captured_url_clone.borrow_mut() = req.get_url_str().to_string();
        Ok(esi::PendingFragmentContent::CompletedRequest(
            fastly::Response::from_body("fragment content"),
        ))
    };

    let processor = Processor::new(
        Some(Request::get("http://example.com/")),
        Configuration::default(), // is_escaped_content = true by default
    );

    processor
        .process_document(reader, &mut output, Some(&dispatcher), None)
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
    let dispatcher = move |req: Request| -> esi::Result<esi::PendingFragmentContent> {
        *captured_url_clone.borrow_mut() = req.get_url_str().to_string();
        Ok(esi::PendingFragmentContent::CompletedRequest(
            fastly::Response::from_body("fragment content"),
        ))
    };

    let processor = Processor::new(
        Some(Request::get("http://example.com/")),
        Configuration::default().with_escaped(false), // Disable HTML entity decoding
    );

    processor
        .process_document(reader, &mut output, Some(&dispatcher), None)
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
    let dispatcher = |_req: Request| -> esi::Result<esi::PendingFragmentContent> {
        let mut resp = fastly::Response::from_body("original content");
        resp.set_header("X-Custom-Header", "original-value");
        Ok(esi::PendingFragmentContent::CompletedRequest(resp))
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

    let processor = Processor::new(
        Some(Request::get("http://example.com/")),
        Configuration::default(),
    );

    processor
        .process_document(
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
    let dispatcher = |req: Request| -> esi::Result<esi::PendingFragmentContent> {
        if req.get_url_str().contains("/main") {
            // Main request fails
            Err(esi::ExecutionError::ExpressionError(
                "main failed".to_string(),
            ))
        } else {
            // Alt request succeeds
            Ok(esi::PendingFragmentContent::CompletedRequest(
                fastly::Response::from_body("alt content"),
            ))
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

    let processor = Processor::new(
        Some(Request::get("http://example.com/")),
        Configuration::default(),
    );

    processor
        .process_document(
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
    let dispatcher = |_req: Request| -> esi::Result<esi::PendingFragmentContent> {
        Ok(esi::PendingFragmentContent::CompletedRequest(
            fastly::Response::from_body("content"),
        ))
    };

    // Response processor that returns an error
    let processor_callback =
        |_req: &mut Request, _resp: fastly::Response| -> esi::Result<fastly::Response> {
            Err(esi::ExecutionError::ExpressionError(
                "processing failed".to_string(),
            ))
        };

    let processor = Processor::new(
        Some(Request::get("http://example.com/")),
        Configuration::default(),
    );

    let result = processor.process_document(
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
    let dispatcher = move |req: Request| -> esi::Result<esi::PendingFragmentContent> {
        if req.get_url_str().contains("/main") {
            // Main request fails
            Err(esi::ExecutionError::ExpressionError(
                "main failed".to_string(),
            ))
        } else {
            // Alt request succeeds - capture the URL
            *captured_alt_url_clone.borrow_mut() = req.get_url_str().to_string();
            Ok(esi::PendingFragmentContent::CompletedRequest(
                fastly::Response::from_body("alt content"),
            ))
        }
    };

    let processor = Processor::new(
        Some(Request::get("http://example.com/?fallback_id=12345")),
        Configuration::default(),
    );

    processor
        .process_document(reader, &mut output, Some(&dispatcher), None)
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
    let dispatcher = move |req: Request| -> esi::Result<esi::PendingFragmentContent> {
        if req.get_url_str().contains("/main") {
            // Main request fails
            Err(esi::ExecutionError::ExpressionError(
                "main failed".to_string(),
            ))
        } else {
            // Alt request succeeds - capture the URL
            *captured_alt_url_clone.borrow_mut() = req.get_url_str().to_string();
            Ok(esi::PendingFragmentContent::CompletedRequest(
                fastly::Response::from_body("alt with function"),
            ))
        }
    };

    let mut req = Request::get("http://Example.COM/");
    req.set_header("Host", "Example.COM");

    let processor = Processor::new(Some(req), Configuration::default());

    processor
        .process_document(reader, &mut output, Some(&dispatcher), None)
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
