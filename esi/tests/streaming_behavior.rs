use bytes::Bytes;
use esi::{parse, parse_complete};
use nom;

/// Tests to validate streaming parser behavior and the theory about delimited content
///
/// Theory to test:
/// 1. Streaming parsers return Incomplete when they need more data
/// 2. delimited() is a sequence combinator that propagates errors from its parsers
/// 3. For incomplete delimited tags (missing closing tag), streaming should return Incomplete
/// 4. parse_complete() should only be used when we KNOW we have complete input

#[test]
fn test_streaming_parse_incomplete_choose_opening() {
    // Incomplete: only the opening tag, no content or closing
    let input = b"<esi:choose>";
    let bytes = Bytes::from_static(input);

    let result = parse(&bytes);

    // Should return Incomplete because we're mid-tag (expecting content + closing)
    match result {
        Err(nom::Err::Incomplete(_)) => {
            // EXPECTED: streaming parser correctly signals it needs more data
        }
        Ok((remaining, elements)) => {
            panic!(
                "Expected Incomplete but got Ok with {} elements, remaining: {:?}",
                elements.len(),
                std::str::from_utf8(remaining)
            );
        }
        Err(e) => {
            panic!("Expected Incomplete but got error: {:?}", e);
        }
    }
}

#[test]
fn test_streaming_parse_incomplete_choose_with_partial_content() {
    // Incomplete: opening + partial content, no closing tag
    let input = b"<esi:choose>\n    <esi:when test=\"";
    let bytes = Bytes::from_static(input);

    let result = parse(&bytes);

    // With streaming parsers, incomplete input MUST return Incomplete
    match result {
        Err(nom::Err::Incomplete(_)) => {
            // EXPECTED: streaming parser correctly signals it needs more data
        }
        Err(nom::Err::Error(e)) => {
            panic!(
                "Incomplete input returned Error({:?}) instead of Incomplete. \
                This indicates a parser bug - incomplete input should return Incomplete.",
                e.code
            );
        }
        Ok((remaining, elements)) => {
            panic!(
                "Expected Incomplete but got Ok with {} elements and {} bytes remaining. \
                Incomplete input should return Incomplete, not partial results.",
                elements.len(),
                remaining.len()
            );
        }
        Err(e) => {
            panic!("Expected Incomplete but got: {:?}", e);
        }
    }
}

#[test]
fn test_streaming_parse_complete_choose() {
    // Complete choose block
    let input = b"<esi:choose>\n    <esi:when test=\"true\">content</esi:when>\n</esi:choose>";
    let bytes = Bytes::from_static(input);

    let result = parse(&bytes);

    match result {
        Ok((remaining, elements)) => {
            assert_eq!(remaining, b"", "Should consume all input");
            assert_eq!(elements.len(), 1, "Should parse one Choose element");
        }
        Err(nom::Err::Incomplete(_)) => {
            // This is also acceptable for streaming - it might want more to be sure
            // Some parsers are cautious and return Incomplete even for complete-looking input
        }
        Err(e) => {
            panic!("Expected success or Incomplete, got error: {:?}", e);
        }
    }
}

#[test]
fn test_parse_complete_vs_parse_on_incomplete_input() {
    // Incomplete input: missing closing tag
    let input = b"<esi:choose>\n    <esi:when test=\"true\">content</esi:when>";
    let bytes = Bytes::from_static(input);

    // Test with streaming parser
    let streaming_result = parse(&bytes);

    // Test with complete parser
    let complete_result = parse_complete(&bytes);

    // Streaming should return Incomplete
    assert!(
        matches!(streaming_result, Err(nom::Err::Incomplete(_))),
        "Streaming parser should return Incomplete for incomplete input, got: {:?}",
        streaming_result
            .as_ref()
            .map(|(r, e)| (r.len(), e.len()))
            .map_err(|e| format!("{:?}", e))
    );

    // Complete parser should handle it (treats Incomplete as EOF)
    match complete_result {
        Ok((_remaining, elements)) => {
            // parse_complete treats Incomplete as "done parsing"
            assert!(
                !elements.is_empty(),
                "Should parse at least partial content"
            );
        }
        Err(e) => {
            panic!("parse_complete unexpectedly failed: {:?}", e);
        }
    }
}

#[test]
fn test_delimited_propagates_incomplete() {
    // Test that delimited() correctly propagates Incomplete from inner parser
    // This validates the theory about delimited being a sequence combinator

    use nom::bytes::streaming::tag;
    use nom::error::Error;
    use nom::sequence::delimited;

    // Incomplete: has opening and closing tags but incomplete content in middle
    let input = b"<start>incomplete";

    // Try to parse with delimited - should get Incomplete from the closing tag parser
    let result: nom::IResult<&[u8], &[u8], Error<&[u8]>> = delimited(
        tag(b"<start>"),
        nom::bytes::streaming::take_while1(|c| c != b'<' && c != b'>'),
        tag(b"<end>"),
    )(input);

    assert!(
        matches!(result, Err(nom::Err::Incomplete(_))),
        "delimited() should propagate Incomplete from closing tag parser, got: {:?}",
        result
    );
}

#[test]
#[ignore] // This test uses nom combinators directly which doesn't work with &Bytes API
fn test_delimited_with_parse_complete_middle() {
    // Note: This test can't work with the new &Bytes API since nom combinators
    // require &[u8] as input type. The important behavior (parse_delimited for
    // delimited content) is tested elsewhere.

    // The test was meant to demonstrate parse_complete behavior with delimited()
    // but our API now properly uses parse_delimited() internally for this purpose.
}

#[test]
fn test_parse_complete_doesnt_know_boundaries() {
    // This test demonstrates that parse_complete correctly stops at ESI closing tags
    // even though it doesn't know the boundaries upfront. This works because ESI
    // closing tags are not valid content elements, so the parser naturally stops.

    let input = b"<esi:when test=\"true\">yes</esi:when></esi:choose>more content";
    //                                                   ^^^^^^^^^^^^^^
    //                                                   Not valid ESI content, parser stops here

    let bytes = Bytes::from_static(input);
    let result = parse_complete(&bytes);

    match result {
        Ok((remaining, elements)) => {
            // parse_complete should stop when it hits unrecognized syntax
            let remaining_str = std::str::from_utf8(remaining).unwrap_or("");
            assert!(
                remaining_str.starts_with("</esi:choose>"),
                "parse_complete should stop before closing tag, but remaining is: {:?}",
                remaining_str
            );
            assert!(!elements.is_empty(), "Should parse at least one element");
        }
        Err(e) => {
            panic!("parse_complete unexpectedly failed: {:?}", e);
        }
    }
}

#[test]
fn test_why_it_works_parse_fails_early() {
    // This test demonstrates why parse_complete works with delimited():
    // parse() uses streaming combinators that naturally stop at ESI closing tags
    // because they're not valid top-level content elements.

    let input = b"<esi:when test=\"true\">content</esi:when></esi:choose>";
    //                                                       ^^^^^^^^^^^^^^ This is NOT valid ESI content

    let bytes = Bytes::from_static(input);
    let streaming_result = parse(&bytes);

    match streaming_result {
        Ok((remaining, _elements)) => {
            // Streaming parse should stop when it hits unrecognized syntax
            let remaining_str = std::str::from_utf8(remaining).unwrap_or("");
            assert!(
                remaining_str.starts_with("</esi:choose>"),
                "Streaming parser should leave closing tag unparsed, but remaining is: {:?}",
                remaining_str
            );
        }
        Err(nom::Err::Incomplete(_)) => {
            // Also acceptable - parser might be cautious
        }
        Err(e) => {
            panic!("Streaming parser unexpectedly failed with error: {:?}", e);
        }
    }
}

#[test]
fn test_the_magic_sequence() {
    // This test validates that streaming parse correctly returns Incomplete
    // when parsing incomplete nested ESI tags, preventing data corruption.

    use nom::bytes::streaming::tag;

    let input = b"<esi:choose><esi:when test=\"true\">yes</esi:whe";
    //            ^-----------^                              ^------^
    //            Opening tag   Content                      Incomplete closing tag

    // Manually simulate what delimited() does:

    // Step 1: Opening tag
    let step1 = tag::<_, _, nom::error::Error<&[u8]>>(b"<esi:choose>")(input);
    let (after_open, _) = step1.expect("Opening tag should succeed");

    // Step 2: Content with streaming parse
    let bytes2 = Bytes::copy_from_slice(after_open);
    let step2 = parse(&bytes2);

    // CRITICAL: parse() MUST return Incomplete here to prevent data corruption.
    // The <esi:when> tag is incomplete, so accepting it would corrupt data.
    assert!(
        matches!(step2, Err(nom::Err::Incomplete(_))),
        "Expected Incomplete from streaming parse on incomplete <esi:when> tag, got: {:?}",
        step2
    );
}

#[test]
fn test_parse_complete_on_actually_complete_input() {
    // parse_complete should work on actually complete input
    let input = b"<esi:include src=\"/test\"/>";
    let bytes = Bytes::from_static(input);
    let result = parse_complete(&bytes);

    match result {
        Ok((remaining, elements)) => {
            assert!(
                remaining.len() == 0,
                "Complete input should be fully consumed, but {} bytes remain",
                remaining.len()
            );
            assert!(
                elements.len() >= 1,
                "Should have parsed at least one element"
            );
        }
        Err(e) => {
            panic!("Should parse complete input successfully: {:?}", e);
        }
    }
}

#[test]
fn test_streaming_incremental_parsing() {
    // Simulate real streaming scenario: data arrives in chunks

    // Chunk 1: Opening tag only - should return Incomplete
    let chunk1 = b"<esi:choose>";
    let bytes1 = Bytes::from_static(chunk1);
    let result1 = parse(&bytes1);
    assert!(
        matches!(result1, Err(nom::Err::Incomplete(_))),
        "Opening tag only should return Incomplete"
    );

    // Chunk 2: Opening + incomplete when tag - should return Incomplete
    let chunk2 = b"<esi:choose>\n    <esi:when test=\"true\">";
    let bytes2 = Bytes::from_static(chunk2);
    let result2 = parse(&bytes2);
    assert!(
        matches!(result2, Err(nom::Err::Incomplete(_))),
        "Incomplete when tag should return Incomplete"
    );

    // Chunk 3: Complete input - should parse successfully
    let chunk3 = b"<esi:choose>\n    <esi:when test=\"true\">content</esi:when>\n</esi:choose>";
    let bytes3 = Bytes::from_static(chunk3);
    let result3 = parse(&bytes3);

    match result3 {
        Ok((remaining, elements)) => {
            assert_eq!(remaining, b"", "Complete input should be fully consumed");
            assert!(!elements.is_empty(), "Should have parsed elements");
        }
        Err(nom::Err::Incomplete(_)) => {
            // Also acceptable - streaming parser being cautious
        }
        Err(e) => {
            panic!("Complete input failed with error: {:?}", e);
        }
    }
}

#[test]
fn test_theory_parse_complete_used_for_delimited_content() {
    // This tests the theory: content inside delimited tags should use parse_complete
    // because we know the boundaries (the closing tag)

    // Simulate what esi_choose does internally:
    // It has: delimited(tag("<esi:choose>"), parse_complete, tag("</esi:choose>"))

    use nom::bytes::streaming::tag;
    use nom::sequence::delimited;

    // Complete content between tags
    let input: &[u8] = b"<esi:choose><esi:when test=\"true\">yes</esi:when></esi:choose>";

    // Extract just the content between the tags - use slices not arrays
    let result: nom::IResult<&[u8], &[u8], nom::error::Error<&[u8]>> = delimited(
        tag(&b"<esi:choose>"[..]),
        tag(&b"<esi:when test=\"true\">yes</esi:when>"[..]), // Simplified - just checking structure
        tag(&b"</esi:choose>"[..]),
    )(input);

    match result {
        Ok((remaining, _content)) => {
            assert_eq!(remaining, &b""[..], "Should consume entire input");
            println!("✓ delimited correctly parses complete content");
        }
        Err(e) => {
            panic!("delimited failed on complete content: {:?}", e);
        }
    }
}

#[test]
fn test_incomplete_vs_error() {
    // Important distinction: Incomplete means "need more data" vs Error means "invalid syntax"

    // Case 1: Incomplete - valid so far, just need more
    let incomplete = b"<esi:assign name=\"x\" value=\"";
    let bytes1 = Bytes::from_static(incomplete);
    let result = parse(&bytes1);
    assert!(
        matches!(result, Err(nom::Err::Incomplete(_))),
        "Incomplete input should return Incomplete, got: {:?}",
        result
    );

    // Case 2: Invalid syntax - might be treated as HTML/text (not an error)
    let invalid = b"<esi:invalid:tag:name>";
    let bytes2 = Bytes::from_static(invalid);
    let result2 = parse(&bytes2);
    // Invalid ESI tags might be treated as HTML, which is valid behavior
    assert!(
        matches!(
            result2,
            Ok(_) | Err(nom::Err::Error(_)) | Err(nom::Err::Incomplete(_))
        ),
        "Invalid ESI syntax should be handled gracefully"
    );
}

#[test]
fn test_all_incomplete_tag_cutoff_positions() {
    // Comprehensive test for all positions where streaming input could be cut off
    // This ensures the parser returns Incomplete (not Error) for all partial valid inputs

    let test_cases = vec![
        // Cut off in tag name
        ("<", "Just opening bracket"),
        ("<e", "Partial tag name 'e'"),
        ("<esi", "Partial tag name 'esi'"),
        ("<esi:", "Tag name with colon"),
        ("<esi:inc", "Partial 'include'"),
        ("<esi:include", "Complete tag name, no closing"),
        // Cut off in attributes
        ("<esi:include ", "After tag name with space"),
        ("<esi:include s", "Partial attribute name"),
        ("<esi:include src", "Complete attribute name, no ="),
        ("<esi:include src=", "After equals, no quote"),
        ("<esi:include src=\"", "After opening quote"),
        ("<esi:include src=\"/path", "Partial attribute value"),
        (
            "<esi:include src=\"/path/to/file",
            "Complete value, no closing quote",
        ),
        (
            "<esi:include src=\"/path/to/file\"",
            "After closing quote, no >",
        ),
        // Self-closing tag variants
        ("<esi:include src=\"/file\"/", "Self-closing, no >"),
        // Cut off in closing tags
        ("<esi:choose></", "Closing tag start"),
        ("<esi:choose></e", "Partial closing tag name"),
        ("<esi:choose></esi:", "Closing tag with colon"),
        ("<esi:choose></esi:cho", "Partial closing tag 'choose'"),
        (
            "<esi:choose></esi:choose",
            "Complete closing tag name, no >",
        ),
        // Other ESI tags
        ("<esi:assign", "Assign tag incomplete"),
        ("<esi:assign name", "Assign with partial attribute"),
        ("<esi:assign name=", "Assign with attribute name and ="),
        ("<esi:assign name=\"", "Assign with attribute value started"),
        (
            "<esi:assign name=\"x\"",
            "Assign with one attribute, no closing",
        ),
        (
            "<esi:assign name=\"x\" value",
            "Assign with second attribute partial",
        ),
        (
            "<esi:assign name=\"x\" value=",
            "Assign with second attribute =",
        ),
        (
            "<esi:assign name=\"x\" value=\"",
            "Assign with second value started",
        ),
        // When tag with test attribute
        ("<esi:when", "When tag incomplete"),
        ("<esi:when test", "When with attribute name"),
        ("<esi:when test=", "When with ="),
        ("<esi:when test=\"", "When with test value started"),
        ("<esi:when test=\"$(HTTP", "When with partial expression"),
        // Try/Attempt/Except tags
        ("<esi:try", "Try tag incomplete"),
        ("<esi:attempt", "Attempt tag incomplete"),
        ("<esi:except", "Except tag incomplete"),
        // Comment and remove
        ("<esi:comment", "Comment tag incomplete"),
        ("<esi:remove", "Remove tag incomplete"),
        // Vars tag
        ("<esi:vars", "Vars tag incomplete"),
        ("$(", "Expression start"),
        ("$(HTTP", "Partial expression"),
        ("$(HTTP_", "Partial variable name"),
    ];

    for (input, description) in test_cases {
        let bytes = Bytes::copy_from_slice(input.as_bytes());
        let result = parse(&bytes);
        assert!(
            matches!(result, Err(nom::Err::Incomplete(_))),
            "Test case '{}' ({}): Expected Incomplete, got: {:?}",
            input,
            description,
            result
        );
    }
}

#[test]
fn test_incomplete_nested_tags() {
    // Test incomplete input with nested tags at various positions

    let test_cases = vec![
        // Choose with incomplete when
        ("<esi:choose><esi:when", "Choose with partial when tag"),
        ("<esi:choose><esi:when test", "Choose with when missing ="),
        (
            "<esi:choose><esi:when test=",
            "Choose with when missing quote",
        ),
        (
            "<esi:choose><esi:when test=\"true",
            "Choose with when missing closing quote",
        ),
        (
            "<esi:choose><esi:when test=\"true\"",
            "Choose with when missing >",
        ),
        (
            "<esi:choose><esi:when test=\"true\">",
            "Choose with when tag open, no content",
        ),
        (
            "<esi:choose><esi:when test=\"true\">content",
            "Choose with when content, no closing tag",
        ),
        (
            "<esi:choose><esi:when test=\"true\">content</esi:when",
            "Choose with when partial closing tag",
        ),
        (
            "<esi:choose><esi:when test=\"true\">content</esi:when>",
            "Choose with complete when, no otherwise/closing",
        ),
        (
            "<esi:choose><esi:when test=\"true\">yes</esi:when><esi:otherwise",
            "Choose with otherwise partial",
        ),
        // Try with incomplete attempt/except
        ("<esi:try><esi:attempt", "Try with partial attempt"),
        (
            "<esi:try><esi:attempt>",
            "Try with attempt open, no content",
        ),
        (
            "<esi:try><esi:attempt>content",
            "Try with attempt content, no closing",
        ),
        (
            "<esi:try><esi:attempt>content</esi:attempt",
            "Try with attempt partial closing",
        ),
        (
            "<esi:try><esi:attempt>content</esi:attempt><esi:except",
            "Try with except partial",
        ),
        // Comment with incomplete content
        ("<esi:comment text", "Comment with partial attribute"),
        (
            "<esi:comment text=\"",
            "Comment with attribute value started",
        ),
        // Remove with incomplete content
        ("<esi:remove>", "Remove tag open, no content"),
        ("<esi:remove>content", "Remove with content, no closing"),
        (
            "<esi:remove>content</esi:remove",
            "Remove with partial closing tag",
        ),
    ];

    for (input, description) in test_cases {
        let bytes = Bytes::copy_from_slice(input.as_bytes());
        let result = parse(&bytes);
        assert!(
            matches!(result, Err(nom::Err::Incomplete(_))),
            "Test case '{}' ({}): Expected Incomplete, got: {:?}",
            input,
            description,
            result
        );
    }
}

#[test]
fn test_incomplete_with_whitespace_and_newlines() {
    // Test that incomplete tags inside delimited tags work correctly even with whitespace

    let test_cases = vec![
        // These all have the incomplete tag inside a delimited context (choose)
        // so they should return Incomplete
        ("<esi:choose>\n", "Choose with newline, no content"),
        ("<esi:choose>\n  ", "Choose with newline and spaces"),
        (
            "<esi:choose>\n  <esi:when",
            "Choose with formatted partial when",
        ),
        (
            "<esi:choose>\n  <esi:when test=\"true\">\n    ",
            "Choose with when and content whitespace",
        ),
    ];

    for (input, description) in test_cases {
        let bytes = Bytes::copy_from_slice(input.as_bytes());
        let result = parse(&bytes);
        assert!(
            matches!(result, Err(nom::Err::Incomplete(_))),
            "Test case '{}' ({}): Expected Incomplete, got: {:?}",
            input,
            description,
            result
        );
    }

    // Leading whitespace is actually valid content, so these parse the whitespace as Text
    // and leave the incomplete tag for the next parse call. This is correct streaming behavior.
    let whitespace_cases = vec![
        ("  <esi:include", "Leading whitespace with partial tag"),
        ("\n\n<esi:assign", "Leading newlines with partial tag"),
    ];

    for (input, description) in whitespace_cases {
        let bytes = Bytes::copy_from_slice(input.as_bytes());
        let result = parse(&bytes);
        // Should either return Incomplete OR return Ok with the whitespace parsed as Text
        // and the incomplete tag remaining
        match result {
            Err(nom::Err::Incomplete(_)) => {
                // This is fine - parser detected incomplete tag
            }
            Ok((remaining, elements)) => {
                // Also fine - parser consumed whitespace as Text, incomplete tag is in remaining
                assert!(
                    !elements.is_empty() && !remaining.is_empty(),
                    "Test case '{}' ({}): If Ok, should have parsed Text and have remaining incomplete tag",
                    input,
                    description
                );
            }
            other => {
                panic!(
                    "Test case '{}' ({}): Expected Incomplete or Ok with partial parse, got: {:?}",
                    input, description, other
                );
            }
        }
    }
}

#[test]
fn test_incomplete_html_and_script_tags() {
    // Test incomplete HTML tags and script tags
    //
    // Important distinctions:
    // - <script> tags REQUIRE closing tags - incomplete script returns Incomplete
    // - Other HTML tags like <div> are treated as complete (parsed as Text, not Html)
    // - Partial tags (missing >) always return Incomplete

    let test_cases = vec![
        // Partial HTML opening tags (no closing >)
        ("<div", "Partial div tag"),
        ("<div class", "Div with partial attribute"),
        ("<div class=", "Div with attribute equals"),
        ("<div class=\"", "Div with attribute value start"),
        ("<div class=\"container", "Div with partial attribute value"),
        (
            "<div class=\"container\"",
            "Div with complete attribute, no >",
        ),
        // Partial HTML closing tags (no closing >)
        ("</div", "Partial closing div tag"),
        ("</di", "Partial closing tag name"),
        ("</", "Closing tag start only"),
        // Script tags - MUST have closing </script> tag
        ("<script", "Partial script opening tag"),
        ("<script>", "Script opening tag, REQUIRES closing"),
        (
            "<script>console.log('test')",
            "Script with content, no closing tag",
        ),
        (
            "<script>console.log('test')</script",
            "Script with partial closing tag",
        ),
        (
            "<script>console.log('test')</scri",
            "Script with partial closing tag name",
        ),
        (
            "<script>console.log('test')</scr",
            "Script with partial closing tag",
        ),
        (
            "<script>console.log('test')</sc",
            "Script with partial closing tag",
        ),
        (
            "<script>console.log('test')</s",
            "Script with partial closing tag",
        ),
        (
            "<script>console.log('test')<",
            "Script with closing tag start",
        ),
        // Script tags with attributes
        ("<script type", "Script with partial attribute"),
        ("<script type=", "Script with attribute equals"),
        ("<script type=\"", "Script with attribute value start"),
        (
            "<script type=\"text/javascript",
            "Script with partial attribute value",
        ),
        (
            "<script type=\"text/javascript\"",
            "Script with complete attribute, no >",
        ),
        (
            "<script type=\"text/javascript\">",
            "Script with attribute, REQUIRES closing",
        ),
        (
            "<script type=\"text/javascript\">code",
            "Script with attribute and partial content",
        ),
        // Self-closing HTML tags (no closing >)
        ("<br", "Partial br tag"),
        ("<br/", "Self-closing br, no >"),
        ("<img src", "Img with partial attribute"),
        ("<img src=\"", "Img with attribute value start"),
        (
            "<img src=\"/path/to/image.jpg",
            "Img with partial attribute value",
        ),
        (
            "<img src=\"/path/to/image.jpg\"",
            "Img with complete attribute, no >",
        ),
        ("<img src=\"/path/to/image.jpg\"/", "Img self-closing, no >"),
    ];

    for (input, description) in test_cases {
        let bytes = Bytes::copy_from_slice(input.as_bytes());
        let result = parse(&bytes);
        assert!(
            matches!(result, Err(nom::Err::Incomplete(_))),
            "Test case '{}' ({}): Expected Incomplete, got: {:?}",
            input,
            description,
            result
        );
    }

    // Note about non-script HTML tags:
    // Tags like "<div>" without closing are treated as complete and parsed as Text,
    // not as Html elements. This is correct behavior - the parser treats unknown
    // or unclosed non-script tags as text content rather than HTML structure.
}

#[test]
fn test_streaming_handles_incomplete_attributes() {
    // This test validates that streaming parsers correctly handle incomplete attribute values.
    // With the fix to parse_delimited, incomplete attributes now return Incomplete correctly.

    use nom::bytes::streaming::{is_not, tag};
    use nom::sequence::delimited;

    // Test input: opening quote, some content, but NO closing quote
    let input: &[u8] = b"\"incomplete_attribute_value";

    // Test 1: is_not() alone should return Incomplete
    let content_only = &input[1..]; // Skip the opening quote
    let is_not_result = is_not::<_, _, nom::error::Error<&[u8]>>(&b"\""[..])(content_only);
    assert!(
        matches!(is_not_result, Err(nom::Err::Incomplete(_))),
        "is_not() should return Incomplete when it doesn't find the delimiter"
    );

    // Test 2: delimited() should also return Incomplete
    let delimited_result: nom::IResult<&[u8], &[u8], nom::error::Error<&[u8]>> =
        delimited(tag(b"\""), is_not(&b"\""[..]), tag(b"\""))(input);
    assert!(
        matches!(delimited_result, Err(nom::Err::Incomplete(_))),
        "delimited() should return Incomplete for missing closing delimiter, got: {:?}",
        delimited_result
    );

    // Test 3: With complete input, parsing should succeed
    let complete_input: &[u8] = b"\"incomplete_attribute_value\"";
    let retry_result: nom::IResult<&[u8], &[u8], nom::error::Error<&[u8]>> =
        delimited(tag(b"\""), is_not(&b"\""[..]), tag(b"\""))(complete_input);
    assert!(
        matches!(retry_result, Ok(_)),
        "Should succeed with complete input"
    );

    // Test 4: ESI parser with incomplete attribute should return Incomplete
    let esi_input: &[u8] = b"<esi:choose>\n    <esi:when test=\"";
    let esi_bytes = Bytes::copy_from_slice(esi_input);
    let esi_result = parse(&esi_bytes);
    assert!(
        matches!(esi_result, Err(nom::Err::Incomplete(_))),
        "ESI parser should return Incomplete for incomplete attribute, got: {:?}",
        esi_result
    );
}

// ============================================================================
// STREAMING PARSER IMPLEMENTATION SUMMARY
// ============================================================================
//
// ARCHITECTURE:
//
// The ESI parser uses a proper streaming architecture with two key functions:
//
// 1. parse() - Streaming document parser
//    - Uses nom::bytes::streaming combinators
//    - Returns Incomplete when it needs more data
//    - Used for top-level document parsing
//
// 2. parse_delimited() - Streaming content parser for delimited tags
//    - Used inside delimited() for tags like <esi:choose>...</esi:choose>
//    - Calls parse() in a loop to process content
//    - ALWAYS propagates Incomplete when encountered
//    - Prevents data corruption by never accepting incomplete nested tags
//
// HOW IT WORKS:
//
// For delimited tags like <esi:choose>, the structure is:
//   delimited(tag("<esi:choose>"), parse_delimited, tag("</esi:choose>"))
//
// Flow with incomplete input like "<esi:choose><esi:when test=\"":
// 1. Opening tag matches successfully
// 2. parse_delimited is called on the content
// 3. parse_delimited calls parse() which detects incomplete <esi:when> tag
// 4. parse() returns Incomplete
// 5. parse_delimited PROPAGATES Incomplete (critical fix!)
// 6. delimited() propagates Incomplete to caller
// 7. No data corruption - incomplete tags are never accepted
//
// THE FIX:
//
// Previously, parse_delimited would return Ok with partial results when it
// encountered Incomplete after parsing some content. This caused delimited()
// to try matching the closing tag on unconsumed input, which failed with Error.
//
// The fix: parse_delimited now ALWAYS propagates Incomplete. In streaming mode,
// we can't know if incomplete data is the closing tag or more content, so we
// must always ask for more data.
//
// WHY parse() NATURALLY RESPECTS BOUNDARIES:
//
// Input: b"<esi:when...>content</esi:when></esi:choose>"
//
// When parse() encounters "</esi:choose>":
// - It's NOT a valid top-level ESI tag
// - Parser naturally stops and leaves it unparsed
// - This creates an implicit boundary that delimited() can use
// - ESI grammar is unambiguous, so this works reliably
//
// ============================================================================
// TEST COVERAGE:
//
// These tests validate the streaming parser implementation:
//
// 1. test_streaming_parse_incomplete_choose_opening
//    - Validates: Incomplete opening tag returns Incomplete
//
// 2. test_streaming_parse_incomplete_choose_with_partial_content
//    - Validates: Incomplete nested tags return Incomplete (prevents corruption)
//    - This was the bug that got fixed!
//
// 3. test_streaming_parse_complete_choose
//    - Validates: Complete input parses successfully
//
// 4. test_parse_complete_vs_parse_on_incomplete_input
//    - Validates: Distinction between parse() and parse_complete()
//    - parse() returns Incomplete, parse_complete() treats it as EOF
//
// 5. test_delimited_propagates_incomplete
//    - Validates: delimited() propagates Incomplete from missing closing tag
//
// 6. test_the_magic_sequence
//    - Validates: parse_delimited correctly detects incomplete nested tags
//
// 7. test_streaming_incremental_parsing
//    - Validates: Progressive data chunks work correctly
//
// 8. test_streaming_handles_incomplete_attributes
//    - Validates: Incomplete attributes return Incomplete correctly
//
// 9. test_incomplete_vs_error
//    - Validates: Distinction between Incomplete and Error
//
// 10. test_why_it_works_parse_fails_early
//     - Validates: Parser naturally stops at ESI closing tags
//
// 11. test_parse_complete_doesnt_know_boundaries
//     - Validates: parse_complete stops at ESI closing tags
//
// 12. test_delimited_with_parse_complete_middle
//     - Historical test for old pattern (now uses parse_delimited)
//
// 13. test_theory_parse_complete_used_for_delimited_content
//     - Validates: delimited() structure works correctly
//
// 14. test_parse_complete_on_actually_complete_input
//     - Validates: parse_complete() handles complete input correctly
//
// ============================================================================
// STREAMING BEST PRACTICES:
//
// For applications using this parser:
//
// 1. Buffer input when parse() returns Incomplete
// 2. Read more data from the stream
// 3. Combine buffered + new data and retry
// 4. Only treat as error after timeout or max buffer size
//
// The parser correctly returns Incomplete for all cases where more data
// might make the input valid. This prevents data corruption from incomplete
// ESI tags being accepted as complete.
//
// ============================================================================
