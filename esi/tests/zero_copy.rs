// Zero-copy parser tests
// These tests verify that parse_complete() works correctly with esi:try, esi:choose, esi:remove

use bytes::Bytes;
use esi::{parse_complete, parser_types::{Element, Tag}};

#[test]
fn test_zero_copy_esi_try() {
    let input = Bytes::from_static(br#"<esi:try>
<esi:attempt>
attempt content
</esi:attempt>
<esi:except>
except content
</esi:except>
</esi:try>"#);
    
    let (remaining, elements) = parse_complete(&input).expect("should parse");
    assert_eq!(remaining, b"");
    
    // Find the Try tag
    let try_found = elements.iter().any(|element| {
        matches!(element, Element::Esi(Tag::Try { attempt_events, except_events })
            if attempt_events.len() == 1 && !except_events.is_empty())
    });
    
    assert!(try_found, "Should find Try tag with attempt and except");
}

#[test]
fn test_zero_copy_esi_try_multiple_attempts() {
    let input = Bytes::from_static(br#"<esi:try>
<esi:attempt>first</esi:attempt>
<esi:attempt>second</esi:attempt>
<esi:except>error</esi:except>
</esi:try>"#);
    
    let (remaining, elements) = parse_complete(&input).expect("should parse");
    assert_eq!(remaining, b"");
    
    let try_found = elements.iter().any(|element| {
        matches!(element, Element::Esi(Tag::Try { attempt_events, except_events })
            if attempt_events.len() == 2 && !except_events.is_empty())
    });
    
    assert!(try_found, "Should find Try tag with 2 attempts");
}

#[test]
fn test_zero_copy_esi_choose_simple() {
    let input = Bytes::from_static(br#"<esi:choose>
<esi:when test="$(HTTP_COOKIE{test})">
cookie content
</esi:when>
<esi:otherwise>
default content
</esi:otherwise>
</esi:choose>"#);
    
    let (remaining, elements) = parse_complete(&input).expect("should parse");
    assert_eq!(remaining, b"");
    
    let choose_found = elements.iter().any(|element| {
        matches!(element, Element::Esi(Tag::Choose { when_branches, otherwise_events })
            if when_branches.len() == 1 && !otherwise_events.is_empty())
    });
    
    assert!(choose_found, "Should find Choose tag with when and otherwise");
}

#[test]
fn test_zero_copy_esi_choose_multiple_when() {
    let input = Bytes::from_static(br#"<esi:choose>
<esi:when test="1">first</esi:when>
<esi:when test="2">second</esi:when>
<esi:when test="3">third</esi:when>
<esi:otherwise>default</esi:otherwise>
</esi:choose>"#);
    
    let (remaining, elements) = parse_complete(&input).expect("should parse");
    assert_eq!(remaining, b"");
    
    let choose_found = elements.iter().any(|element| {
        matches!(element, Element::Esi(Tag::Choose { when_branches, otherwise_events })
            if when_branches.len() == 3 && !otherwise_events.is_empty())
    });
    
    assert!(choose_found, "Should find Choose tag with 3 when branches");
}

#[test]
fn test_zero_copy_esi_remove() {
    let input = Bytes::from_static(b"<esi:remove>this should not appear</esi:remove>after");
    
    let (remaining, elements) = parse_complete(&input).expect("should parse");
    assert_eq!(remaining, b"");
    
    // esi:remove should return empty vec for the tag itself, then "after" as text
    let has_text_after = elements.iter().any(|element| {
        matches!(element, Element::Text(bytes) if bytes.as_ref() == b"after")
    });
    
    let no_removed_content = !elements.iter().any(|element| {
        matches!(element, Element::Text(bytes) if bytes.as_ref() == b"this should not appear")
    });
    
    assert!(has_text_after, "Should have text after remove tag");
    assert!(no_removed_content, "Should not have removed content");
}

#[test]
fn test_zero_copy_esi_remove_with_tags_inside() {
    let input = Bytes::from_static(b"<esi:remove><div>content</div><esi:include src=\"x\"/></esi:remove>visible");
    
    let (remaining, elements) = parse_complete(&input).expect("should parse");
    assert_eq!(remaining, b"");
    
    // Everything inside esi:remove should be discarded
    let has_visible = elements.iter().any(|element| {
        matches!(element, Element::Text(bytes) if bytes.as_ref() == b"visible")
    });
    
    let no_div = !elements.iter().any(|element| {
        matches!(element, Element::Html(bytes) if bytes.as_ref().contains(&b'd'))
    });
    
    assert!(has_visible, "Should have visible text");
    assert!(no_div, "Should not have content from inside remove");
}

#[test]
fn test_zero_copy_nested_choose_in_try() {
    let input = Bytes::from_static(br#"<esi:try>
<esi:attempt>
<esi:choose>
<esi:when test="1">nested</esi:when>
</esi:choose>
</esi:attempt>
<esi:except>error</esi:except>
</esi:try>"#);
    
    let (remaining, elements) = parse_complete(&input).expect("should parse");
    assert_eq!(remaining, b"");
    
    // Should successfully parse nested structure
    let has_try = elements.iter().any(|element| {
        matches!(element, Element::Esi(Tag::Try { .. }))
    });
    
    assert!(has_try, "Should parse nested choose inside try");
}

#[test]
fn test_zero_copy_text_before_and_after() {
    let input = Bytes::from_static(b"before<esi:remove>hidden</esi:remove>after");
    
    let (remaining, elements) = parse_complete(&input).expect("should parse");
    assert_eq!(remaining, b"");
    
    let has_before = elements.iter().any(|element| {
        matches!(element, Element::Text(bytes) if bytes.as_ref() == b"before")
    });
    
    let has_after = elements.iter().any(|element| {
        matches!(element, Element::Text(bytes) if bytes.as_ref() == b"after")
    });
    
    assert!(has_before && has_after, "Should have text before and after");
}
