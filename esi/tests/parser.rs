// Parser tests for ESI parser
// These tests verify that the parser correctly handles ESI tags and produces the expected AST

use bytes::Bytes;
use esi::parse_remainder;

#[test]
fn test_parse_basic_include() {
    let input = br#"<html><body><esi:include src="https://example.com/hello"/></body></html>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    // Find the Include tag
    let include_found = elements.iter().any(|element| {
        matches!(element, esi::Element::Esi(
            esi::Tag::Include { attrs, .. }
        ) if matches!(&attrs.src, esi::Expr::String(Some(s)) if s == "https://example.com/hello") 
            && attrs.alt.is_none() 
            && !attrs.continue_on_error 
            && attrs.params.is_empty())
    });

    assert!(
        include_found,
        "Should find Include tag with correct attributes"
    );
}

#[test]
fn test_parse_include_with_alt_and_onerror() {
    let input = br#"<esi:include src="abc" alt="def" onerror="continue"/>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let include_found = elements.iter().any(|element| {
        matches!(element, esi::Element::Esi(
            esi::Tag::Include { attrs, .. }
        ) if matches!(&attrs.src, esi::Expr::String(Some(s)) if s == "abc")
            && matches!(&attrs.alt, Some(esi::Expr::String(Some(a))) if a == "def")
            && attrs.continue_on_error 
            && attrs.params.is_empty())
    });

    assert!(
        include_found,
        "Should find Include with alt and continue_on_error"
    );
}

#[test]
fn test_parse_open_close_include() {
    let input = br#"<esi:include src="abc" alt="def" onerror="continue"></esi:include>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let include_found = elements.iter().any(|element| {
        matches!(element, esi::Element::Esi(
            esi::Tag::Include { attrs, .. }
        ) if matches!(&attrs.src, esi::Expr::String(Some(s)) if s == "abc")
            && matches!(&attrs.alt, Some(esi::Expr::String(Some(a))) if a == "def")
            && attrs.continue_on_error
            && attrs.params.is_empty())
    });

    assert!(include_found, "Should parse open-close include tag");
}

#[test]
fn test_parse_include_with_onerror() {
    let input = br#"<esi:include src="/_fragments/content.html" onerror="continue"/>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let include_found = elements.iter().any(|element| {
        matches!(element, esi::Element::Esi(
            esi::Tag::Include { attrs, .. }
        ) if matches!(&attrs.src, esi::Expr::String(Some(s)) if s == "/_fragments/content.html")
            && attrs.alt.is_none() 
            && attrs.continue_on_error 
            && attrs.params.is_empty())
    });

    assert!(include_found, "Should find Include with onerror=continue");
}

#[test]
fn test_parse_include_with_single_param() {
    let input = br#"<esi:include src="/fragment">
    <esi:param name="foo" value="bar"/>
</esi:include>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let include_found = elements.iter().any(|element| {
        matches!(element, esi::Element::Esi(
            esi::Tag::Include { attrs, .. }
        ) if matches!(&attrs.src, esi::Expr::String(Some(s)) if s == "/fragment")
            && attrs.alt.is_none() 
            && !attrs.continue_on_error 
            && attrs.params.len() == 1
            && attrs.params[0].0 == "foo"
            && matches!(&attrs.params[0].1, esi::Expr::String(Some(v)) if v == "bar"))
    });

    assert!(include_found, "Should find Include with one param");
}

#[test]
fn test_parse_include_with_multiple_params() {
    let input = br#"<esi:include src="/fragment" alt="/fallback" onerror="continue">
    <esi:param name="user" value="alice"/>
    <esi:param name="role" value="admin"/>
    <esi:param name="id" value="123"/>
</esi:include>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let include_found = elements.iter().any(|element| {
        matches!(element, esi::Element::Esi(
            esi::Tag::Include { attrs, .. }
        ) if matches!(&attrs.src, esi::Expr::String(Some(s)) if s == "/fragment")
            && matches!(&attrs.alt, Some(esi::Expr::String(Some(a))) if a == "/fallback")
            && attrs.continue_on_error 
            && attrs.params.len() == 3
            && attrs.params[0].0 == "user" && matches!(&attrs.params[0].1, esi::Expr::String(Some(v)) if v == "alice")
            && attrs.params[1].0 == "role" && matches!(&attrs.params[1].1, esi::Expr::String(Some(v)) if v == "admin")
            && attrs.params[2].0 == "id" && matches!(&attrs.params[2].1, esi::Expr::Integer(123)))
    });

    assert!(include_found, "Should find Include with multiple params");
}

#[test]
fn test_parse_include_self_closing_has_no_params() {
    let input = br#"<esi:include src="/test"/>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let include_found = elements.iter().any(|element| {
        matches!(element, esi::Element::Esi(
            esi::Tag::Include { attrs, .. }
        ) if matches!(&attrs.src, esi::Expr::String(Some(s)) if s == "/test") && attrs.params.is_empty())
    });

    assert!(include_found, "Self-closing include should have no params");
}

#[test]
fn test_parse_include_no_store_attribute() {
    let input = br#"<esi:include src="/test" no-store="on"/>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let include_found = elements.iter().any(|element| {
        matches!(element, esi::Element::Esi(
            esi::Tag::Include { attrs, .. }
        ) if matches!(&attrs.src, esi::Expr::String(Some(s)) if s == "/test")
            && attrs.no_store)
    });

    assert!(
        include_found,
        "Should parse include with no-store attribute"
    );
}

#[test]
fn test_parse_include_no_store_off_attribute() {
    let input = br#"<esi:include src="/test" no-store="off"/>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let include_found = elements.iter().any(|element| {
        matches!(element, esi::Element::Esi(
            esi::Tag::Include { attrs, .. }
        ) if matches!(&attrs.src, esi::Expr::String(Some(s)) if s == "/test")
            && !attrs.no_store)
    });

    assert!(
        include_found,
        "Should parse include with no-store=off as cacheable"
    );
}

#[test]
fn test_parse_include_no_store_true_is_not_enabled() {
    let input = br#"<esi:include src="/test" no-store="true"/>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let include_found = elements.iter().any(|element| {
        matches!(element, esi::Element::Esi(
            esi::Tag::Include { attrs, .. }
        ) if matches!(&attrs.src, esi::Expr::String(Some(s)) if s == "/test")
            && !attrs.no_store)
    });

    assert!(
        include_found,
        "no-store=true should not enable no-store; only on/off are supported"
    );
}

#[test]
fn test_parse_include_numbered_header_attributes() {
    let input = br#"<esi:include src="/frag" setheader1="X-A: one" appendheader2="X-B: two" removeheader1="X-C"/>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let include_found = elements.iter().any(|element| {
        matches!(element, esi::Element::Esi(
            esi::Tag::Include { attrs, .. }
        ) if attrs.setheaders.iter().any(|(k, _)| k == "X-A")
            && attrs.appendheaders.iter().any(|(k, _)| k == "X-B")
            && attrs.removeheaders.iter().any(|h| h == "X-C"))
    });

    assert!(
        include_found,
        "Should parse include with numbered set/append/remove header attributes"
    );
}

#[test]
fn test_parse_include_with_query_string_variable() {
    // Example from Akamai ESI spec
    // Mixed text+variable interpolation is now properly parsed at parse-time
    let input =
        br#"<esi:include src="http://search.akamai.com/search?query=$(QUERY_STRING{'query'})"/>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    // The src is parsed as Interpolated with text and expression parts
    let include_found = elements.iter().any(|element| {
        matches!(element, esi::Element::Esi(
            esi::Tag::Include { attrs, .. }
        ) if matches!(&attrs.src, esi::Expr::Interpolated(_)))
    });

    assert!(include_found, "Should find Include with interpolated src");
}

#[test]
fn test_parse_param_value_with_variable_expression() {
    let input = br#"<esi:assign name="var1" value="'variable_2'"/>
<esi:include src="a.xml">
<esi:param name="foo" value="$(var1)"/>
</esi:include>"#;
    let bytes = Bytes::from_static(input);
    let result = parse_remainder(&bytes);

    assert!(
        result.is_ok(),
        "Should parse successfully: {:?}",
        result.err()
    );

    let (remaining, elements) = result.unwrap();
    assert_eq!(remaining, b"");

    // Check what the param value looks like
    let include_found = elements.iter().find_map(|element| {
        if let esi::Element::Esi(esi::Tag::Include { attrs, .. }) = element {
            Some(&attrs.params)
        } else {
            None
        }
    });

    assert!(include_found.is_some(), "Should find include");
    let params = include_found.unwrap();
    assert_eq!(params.len(), 1);
    assert_eq!(params[0].0, "foo");

    // Now the value is parsed as a Variable expression!
    println!("Param value: {:?}", params[0].1);
    assert!(
        matches!(&params[0].1, esi::Expr::Variable(name, _, _) if name == "var1"),
        "Param value should be parsed as a Variable expression"
    );
}

#[test]
fn test_parse_try_with_attempt_and_except() {
    let input = br#"
<esi:try>
    <esi:attempt>
        <esi:include src="/abc"/>
    </esi:attempt>
    <esi:except>
        <esi:include src="/xyz"/>
        <a href="/efg"/>
        just text
    </esi:except>
</esi:try>"#;

    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");
    assert_eq!(remaining, b"");

    // Find the Try tag
    let try_tag_found = elements.iter().any(|element| {
        if let esi::Element::Esi(esi::Tag::Try {
            attempt_events,
            except_events,
        }) = element
        {
            // Check attempt contains include for /abc
            let attempt_has_abc = attempt_events.iter().any(|attempt_elements| {
                attempt_elements.iter().any(|c| {
                    matches!(c, esi::Element::Esi(
                        esi::Tag::Include { attrs, .. }
                    ) if matches!(&attrs.src, esi::Expr::String(Some(s)) if s == "/abc"))
                })
            });

            // Check except contains include for /xyz
            let except_has_xyz = except_events.iter().any(|c| {
                matches!(c, esi::Element::Esi(
                    esi::Tag::Include { attrs, .. }
                ) if matches!(&attrs.src, esi::Expr::String(Some(s)) if s == "/xyz"))
            });

            attempt_has_abc && except_has_xyz
        } else {
            false
        }
    });

    assert!(
        try_tag_found,
        "Should find Try tag with correct attempt and except branches"
    );
}

#[test]
fn test_parse_nested_try() {
    let input = br#"<esi:try>
    <esi:attempt>
        <esi:include src="/abc"/>
        <esi:try>
            <esi:attempt>
                <esi:include src="/foo"/>
            </esi:attempt>
            <esi:except>
                <esi:include src="/bar"/>
            </esi:except>
        </esi:try>
    </esi:attempt>
    <esi:except>
        <esi:include src="/xyz"/>
    </esi:except>
</esi:try>"#;

    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");
    assert_eq!(remaining, b"");

    // Find outer Try tag
    let nested_try_found = elements.iter().any(|element| {
        if let esi::Element::Esi(esi::Tag::Try {
            attempt_events,
            except_events,
        }) = element
        {
            // Check outer attempt contains /abc
            let has_abc = attempt_events.iter().any(|attempt_elements| {
                attempt_elements.iter().any(|c| {
                    matches!(c, esi::Element::Esi(
                        esi::Tag::Include { attrs, .. }
                    ) if matches!(&attrs.src, esi::Expr::String(Some(s)) if s == "/abc"))
                })
            });

            // Check outer attempt contains nested Try
            let has_nested_try = attempt_events.iter().any(|attempt_elements| {
                attempt_elements
                    .iter()
                    .any(|c| matches!(c, esi::Element::Esi(esi::Tag::Try { .. })))
            });

            // Check outer except contains /xyz
            let has_xyz = except_events.iter().any(|c| {
                matches!(c, esi::Element::Esi(
                    esi::Tag::Include { attrs, .. }
                ) if matches!(&attrs.src, esi::Expr::String(Some(s)) if s == "/xyz"))
            });

            has_abc && has_nested_try && has_xyz
        } else {
            false
        }
    });

    assert!(nested_try_found, "Should parse nested try blocks correctly");
}

#[test]
fn test_parse_assign() {
    let input = br#"<esi:assign name="foo" value="bar"/>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let assign_found = elements.iter().any(|element| {
        if let esi::Element::Esi(esi::Tag::Assign {
            name,
            subscript: _,
            value,
        }) = element
        {
            // Value is now a pre-parsed Expr
            // "bar" (not a valid ESI expression) becomes Expr::String(Some(ref s)) if s == "bar"
            *name == "foo" && matches!(value, esi::Expr::String(Some(ref s)) if s == "bar")
        } else {
            false
        }
    });

    assert!(
        assign_found,
        "Should find Assign tag with value as String expression"
    );
}

#[test]
fn test_parse_assign_short_with_integer() {
    let input = br#"<esi:assign name="count" value="123"/>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let assign_found = elements.iter().any(|element| {
        if let esi::Element::Esi(esi::Tag::Assign {
            name,
            subscript: _,
            value,
        }) = element
        {
            *name == "count" && *value == esi::Expr::Integer(123)
        } else {
            false
        }
    });

    assert!(assign_found, "Should parse integer value");
}

#[test]
fn test_parse_assign_short_with_variable() {
    let input = br#"<esi:assign name="copy" value="$(HTTP_HOST)"/>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let assign_found = elements.iter().any(|element| {
        if let esi::Element::Esi(esi::Tag::Assign {
            name,
            subscript: _,
            value,
        }) = element
        {
            *name == "copy"
                && matches!(value, esi::Expr::Variable(ref n, None, None) if n == "HTTP_HOST")
        } else {
            false
        }
    });

    assert!(assign_found, "Should parse variable expression");
}

#[test]
fn test_parse_assign_short_with_quoted_string() {
    let input = br#"<esi:assign name="text" value="'hello world'"/>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let assign_found = elements.iter().any(|element| {
        if let esi::Element::Esi(esi::Tag::Assign {
            name,
            subscript: _,
            value,
        }) = element
        {
            *name == "text" && matches!(value, esi::Expr::String(Some(ref s)) if s == "hello world")
        } else {
            false
        }
    });

    assert!(assign_found, "Should parse quoted string expression");
}

#[test]
fn test_parse_assign_long_form() {
    let input = br#"<esi:assign name="message">
        'This is a long form assign'
    </esi:assign>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let assign_found = elements.iter().any(|element| {
        if let esi::Element::Esi(esi::Tag::Assign {
            name,
            subscript: _,
            value,
        }) = element
        {
            *name == "message" && matches!(value, esi::Expr::String(Some(_)))
        } else {
            false
        }
    });

    assert!(assign_found, "Should parse long form assign");
}

#[test]
fn test_parse_assign_long_with_variable() {
    let input = br#"<esi:assign name="host">$(HTTP_HOST)</esi:assign>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let assign_found = elements.iter().any(|element| {
        if let esi::Element::Esi(esi::Tag::Assign {
            name,
            subscript: _,
            value,
        }) = element
        {
            *name == "host"
                && matches!(value, esi::Expr::Variable(ref n, None, None) if n == "HTTP_HOST")
        } else {
            false
        }
    });

    assert!(assign_found, "Should parse long form with variable");
}

#[test]
fn test_parse_assign_with_function() {
    let input = br#"<esi:assign name="result" value="$url_encode('hello world')"/>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let assign_found = elements.iter().any(|element| {
        if let esi::Element::Esi(esi::Tag::Assign {
            name,
            subscript: _,
            value,
        }) = element
        {
            *name == "result" && matches!(value, esi::Expr::Call(ref n, _) if n == "url_encode")
        } else {
            false
        }
    });

    assert!(assign_found, "Should parse function call in value");
}

#[test]
fn test_parse_assign_long_with_interpolation() {
    // Test compound expression with mixed text and variable
    let input = br#"<esi:assign name="message">Hello $(name)!</esi:assign>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let assign_found = elements.iter().any(|element| {
        if let esi::Element::Esi(esi::Tag::Assign {
            name,
            subscript: _,
            value,
        }) = element
        {
            if *name == "message" {
                // Should be an Interpolated expression with multiple elements
                if let esi::Expr::Interpolated(elements) = value {
                    // Should have: "Hello ", $(name), "!"
                    if elements.len() != 3 {
                        return false;
                    }
                    // Check first element is Text("Hello ")
                    let first_ok = if let esi::Element::Content(ref bytes) = elements[0] {
                        &bytes[..] == b"Hello "
                    } else {
                        false
                    };
                    // Check second element is Variable("name", None, None)
                    let second_ok =
                        if let esi::Element::Expr(esi::Expr::Variable(ref n, None, None)) =
                            &elements[1]
                        {
                            n == "name"
                        } else {
                            false
                        };
                    // Check third element is Text("!")
                    let third_ok = if let esi::Element::Content(ref bytes) = elements[2] {
                        &bytes[..] == b"!"
                    } else {
                        false
                    };
                    first_ok && second_ok && third_ok
                } else {
                    false
                }
            } else {
                false
            }
        } else {
            false
        }
    });

    assert!(assign_found, "Should parse long form with interpolation");
}

#[test]
fn test_parse_assign_long_with_multiple_variables() {
    // Test compound expression with multiple variables
    let input = br#"<esi:assign name="full_name">$(first) $(last)</esi:assign>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    let assign_found = elements.iter().any(|element| {
        if let esi::Element::Esi(esi::Tag::Assign {
            name,
            subscript: _,
            value,
        }) = element
        {
            if *name == "full_name" {
                // Should be an Interpolated expression
                matches!(value, esi::Expr::Interpolated(_))
            } else {
                false
            }
        } else {
            false
        }
    });

    assert!(
        assign_found,
        "Should parse long form with multiple variables"
    );
}

#[test]
fn test_parse_vars_short_form() {
    let input = br#"<esi:vars name="$(foo)"/>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    // Short form vars should produce an expression element
    let var_found = elements.iter().any(|element| {
        if let esi::Element::Expr(esi::Expr::Variable(ref n, None, None)) = element {
            n == "foo"
        } else {
            false
        }
    });

    assert!(
        var_found,
        "Should find variable expression from short-form vars"
    );
}

#[test]
fn test_parse_vars_long_form() {
    let input = br#"<esi:vars>$(foo)</esi:vars>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    // Long form vars should produce an expression element
    let var_found = elements.iter().any(|element| {
        if let esi::Element::Expr(esi::Expr::Variable(ref n, None, None)) = element {
            n == "foo"
        } else {
            false
        }
    });

    assert!(
        var_found,
        "Should find variable expression from long-form vars"
    );
}

#[test]
fn test_parse_choose_when_otherwise() {
    let input = br#"
<esi:choose>
    <esi:when test="$(condition)">
        Content when true
    </esi:when>
    <esi:otherwise>
        Content when false
    </esi:otherwise>
</esi:choose>"#;

    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");
    assert_eq!(remaining, b"");

    let choose_found = elements.iter().any(|element| {
        if let esi::Element::Esi(esi::Tag::Choose {
            when_branches,
            otherwise_events,
        }) = element
        {
            let has_when = !when_branches.is_empty();
            let has_otherwise = !otherwise_events.is_empty();

            // Verify the new WhenBranch structure
            if let Some(first_when) = when_branches.first() {
                // Test is now a pre-parsed Expr, so we check it's a Variable expression
                assert!(matches!(first_when.test, esi::Expr::Variable(..)));
                assert!(first_when.match_name.is_none());
                assert!(!first_when.content.is_empty());
            }

            has_when && has_otherwise
        } else {
            false
        }
    });

    assert!(choose_found, "Should parse choose/when/otherwise structure");
}

#[test]
fn test_parse_choose_multiple_when() {
    // Test multiple when branches - only first true one should execute
    let input = br#"
<esi:choose>
    <esi:when test="0">
        First when (false)
    </esi:when>
    <esi:when test="1">
        Second when (true)
    </esi:when>
    <esi:when test="1">
        Third when (also true, but should not execute)
    </esi:when>
    <esi:otherwise>
        Otherwise (should not execute)
    </esi:otherwise>
</esi:choose>"#;

    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");
    assert_eq!(remaining, b"");

    // Verify we have multiple when branches using the new structure
    let choose_found = elements.iter().any(|element| {
        if let esi::Element::Esi(esi::Tag::Choose {
            when_branches,
            otherwise_events,
        }) = element
        {
            // Should have 3 when branches
            assert_eq!(when_branches.len(), 3, "Should have 3 when branches");

            // Verify test expressions are pre-parsed as Integers
            assert_eq!(when_branches[0].test, esi::Expr::Integer(0));
            assert_eq!(when_branches[1].test, esi::Expr::Integer(1));
            assert_eq!(when_branches[2].test, esi::Expr::Integer(1));

            // Should have otherwise content
            assert!(
                !otherwise_events.is_empty(),
                "Should have otherwise content"
            );

            true
        } else {
            false
        }
    });

    assert!(
        choose_found,
        "Should parse choose with multiple when branches"
    );
}

#[test]
fn test_parse_remove() {
    let input =
        br#"<html><esi:remove>This should not appear</esi:remove><body>visible</body></html>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    // esi:remove content should not appear in elements at all
    let has_removed_text = elements.iter().any(|element| {
        if let esi::Element::Content(t) = element {
            // Check if bytes contain the substring
            let needle = b"should not appear";
            t.windows(needle.len()).any(|window| window == needle)
        } else {
            false
        }
    });

    assert!(
        !has_removed_text,
        "Content inside esi:remove should not appear in parsed elements"
    );

    // But visible content should be there
    let has_visible = elements.iter().any(|element| {
        if let esi::Element::Content(t) = element {
            let needle = b"visible";
            t.windows(needle.len()).any(|window| window == needle)
        } else {
            false
        }
    });

    assert!(has_visible, "Content outside esi:remove should be parsed");
}

#[test]
fn test_parse_comment() {
    let input = br#"<html><esi:comment text="This is a comment"/><body>visible</body></html>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    // esi:comment should not produce any elements
    let comment_count = elements
        .iter()
        .filter(|element| matches!(element, esi::Element::Esi(esi::Tag::Vars { .. })))
        .count();

    assert_eq!(comment_count, 0, "Comments should not produce elements");
}

#[test]
fn test_parse_text_tag() {
    let input = br#"<esi:text>This <esi:include src="test"/> should appear as-is</esi:text>"#;
    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");

    assert_eq!(remaining, b"");

    // esi:text content should be plain text, ESI tags inside should not be parsed
    let text_found = elements.iter().any(|element| {
        if let esi::Element::Content(t) = element {
            let needle1 = b"<esi:include";
            let needle2 = b"should appear as-is";
            t.windows(needle1.len()).any(|w| w == needle1)
                && t.windows(needle2.len()).any(|w| w == needle2)
        } else {
            false
        }
    });

    assert!(
        text_found,
        "esi:text content should be treated as plain text"
    );
}

#[test]
fn test_parse_mixed_content() {
    let input = br#"
<html>
    <head><title>Test</title></head>
    <body>
        <esi:vars>Hello $(USER_NAME)</esi:vars>
        <esi:include src="/header"/>
        <p>Some content</p>
        <esi:assign name="foo" value="bar"/>
    </body>
</html>"#;

    let bytes = Bytes::from_static(input);
    let (remaining, elements) = parse_remainder(&bytes).expect("should parse");
    assert_eq!(remaining, b"");

    // Should have HTML, expressions, ESI tags, and text
    let has_html = elements.iter().any(|c| matches!(c, esi::Element::Html(_)));
    let has_expr = elements.iter().any(|c| matches!(c, esi::Element::Expr(_)));
    let has_esi = elements.iter().any(|c| matches!(c, esi::Element::Esi(_)));
    let has_text = elements
        .iter()
        .any(|c| matches!(c, esi::Element::Content(_)));

    assert!(has_html, "Should have HTML elements");
    assert!(has_expr, "Should have expression elements");
    assert!(has_esi, "Should have ESI tag elements");
    assert!(has_text, "Should have text elements");
}

#[test]
fn test_parse_include_with_esi_attributes() {
    // Test TTL attribute
    let input = br#"<esi:include src="/fragment" ttl="120m"/>"#;
    let bytes = Bytes::from_static(input);
    let result = parse_remainder(&bytes);

    match result {
        Ok((remaining, elements)) => {
            assert_eq!(remaining, b"");
            // Just verify that we got some elements
            assert!(!elements.is_empty(), "Should have parsed some elements");
            // Check that at least one is an Include tag
            let has_include = elements
                .iter()
                .any(|e| matches!(e, esi::Element::Esi(esi::Tag::Include { .. })));
            assert!(has_include, "Should have an Include tag");
        }
        Err(e) => {
            panic!("Failed to parse: {:?}", e);
        }
    }
}
