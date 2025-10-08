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

// Invalid standalone bareword
#[test]
fn test_invalid_standalone_bareword() {
    let input = r#"
        <esi:vars>
            bareword
        </esi:vars>
    "#;
    let req = Request::get("http://example.com");
    let result = process_esi_document(input, req);
    assert!(result.is_err(), "Standalone bareword should cause an error");
    if let Err(e) = result {
        assert!(
            e.to_string().contains("ExpressionError"),
            "Error should be an ExpressionError"
        );
    }
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
        "value\nvalue",
        "Bareword and expression subfields should both resolve to 'value'"
    );
}

// Unclosed subfield
// Missing closing bracket in subfield
#[test]
fn test_missing_closing_bracket() {
    let input = r#"
        <esi:vars>
            $(QUERY_STRING{param)
        </esi:vars>
    "#;
    let req = Request::get("http://example.com?param=value");
    let result = process_esi_document(input, req);
    assert!(
        result.is_err(),
        "Missing closing bracket should cause an error"
    );
    if let Err(e) = result {
        assert!(
            e.to_string().contains("unexpected token"),
            "Error should mention unexpected token"
        );
    }
}

// Bareword with special characters
#[test]
fn test_bareword_special_characters() {
    let input = r#"
        <esi:vars>
            $(QUERY_STRING{param-name})
        </esi:vars>
    "#;
    let req = Request::get("http://example.com?param-name=value");
    let result = process_esi_document(input, req);
    // Assume error due to lack of spec clarity on special characters
    assert!(
        result.is_err(),
        "Bareword with special characters should cause an error"
    );
    if let Err(e) = result {
        assert!(
            e.to_string().contains("ExpressionError"),
            "Error should be an ExpressionError"
        );
    }
}

// Compatibility with ESI choose/when
#[test]
fn test_esi_choose_compatibility() {
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
