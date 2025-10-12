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
    debug!("Processing ESI document: {:?}", input);

    // Create a reader from the input string
    let reader = esi::Reader::from_str(input);

    // Create a writer with a Vec buffer to capture the output
    let buffer = Vec::new();
    let cursor = std::io::Cursor::new(buffer);
    let mut writer = esi::Writer::new(cursor);

    // Create the processor and process the document
    let processor = Processor::new(Some(req), Configuration::default());
    processor.process_document(reader, &mut writer, None, None)?;

    // Extract the processed content from the writer
    let output_buffer = writer.into_inner().into_inner();
    let result = String::from_utf8(output_buffer)
        .map_err(|e| Error::msg(format!("Invalid UTF-8 in processed output: {}", e)))?;

    debug!("Processed result: {:?}", result);
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
// #[test]
// fn test_esi_choose_compatibility() {
//     let input = r#"
//         <esi:choose>
//             <esi:when test="$(QUERY_STRING{param}) == 'value'">
//                 Match
//             </esi:when>
//             <esi:otherwise>
//                 Fallback
//             </esi:otherwise>
//         </esi:choose>
//     "#;
//     let req = Request::get("http://example.com?param=value");
//     let result = process_esi_document(input, req).expect("Processing should succeed");
//     assert_eq!(
//         result.trim(),
//         "Match",
//         "ESI choose/when should work with bareword subfield"
//     );
// }

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
