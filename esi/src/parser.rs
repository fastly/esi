use nom::branch::alt;
use nom::bytes::complete::{
    is_not, tag, tag_no_case, take_till, take_until, take_while, take_while1,
};
use nom::character::complete::{alpha1, char, multispace0, multispace1};
use nom::combinator::{map, map_res, opt, recognize, verify};
use nom::error::Error;
use nom::multi::{many0, separated_list0};
use nom::sequence::{delimited, preceded, separated_pair, terminated, tuple};
use nom::{AsChar, IResult};

use crate::parser_types::*;

pub fn parse(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(many0(element), ParseResult::from_results)(input)
}

/// Callback-based parser that invokes a callback for each element as it's parsed
/// This enables streaming processing without building an AST first
pub fn parse_with_callback<'a, F>(
    input: &'a str,
    mut callback: F,
) -> IResult<&'a str, (), Error<&'a str>>
where
    F: FnMut(ParseResult<'a>) -> Result<(), String>,
{
    let mut remaining = input;

    while !remaining.is_empty() {
        match element(remaining) {
            Ok((rest, result)) => {
                // Call the callback with parsed result
                if let Err(_e) = callback(result) {
                    return Err(nom::Err::Failure(Error::new(
                        rest,
                        nom::error::ErrorKind::Fail,
                    )));
                }
                remaining = rest;
            }
            Err(nom::Err::Error(_)) => {
                // No more elements to parse
                break;
            }
            Err(e) => return Err(e),
        }
    }

    Ok((remaining, ()))
}

/// Parses a standalone ESI expression (for use in test attributes, etc.)
pub fn parse_expression(input: &str) -> IResult<&str, Expr<'_>, Error<&str>> {
    expr(input)
}

/// Parses a string that may contain interpolated expressions like $(VAR)
pub fn parse_interpolated_string(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(
        many0(alt((interpolated_expression, interpolated_text))),
        ParseResult::from_results,
    )(input)
}

fn element(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    alt((text, esi_tag, html))(input)
}

fn parse_interpolated(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(many0(interpolated_element), ParseResult::from_results)(input)
}

fn interpolated_element(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    alt((interpolated_text, interpolated_expression, esi_tag, html))(input)
}

fn esi_tag(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    alt((
        esi_assign,
        esi_include,
        esi_vars,
        esi_comment,
        esi_remove,
        esi_text,
        esi_choose,
        esi_try,
        esi_when,
        esi_otherwise,
        esi_attempt,
        esi_except,
    ))(input)
}

fn esi_assign(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    alt((esi_assign_short, esi_assign_long))(input)
}

fn parse_assign_attributes_short<'a>(attrs: Vec<(&'a str, &'a str)>) -> ParseResult<'a> {
    let mut name = "";
    let mut value_str = "";
    for (key, val) in attrs {
        match key.as_bytes() {
            b"name" => name = val,
            b"value" => value_str = val,
            _ => {}
        }
    }

    // Per ESI spec, short form value attribute contains an expression
    // Try to parse as ESI expression. If it fails, treat as string literal.
    let value = match parse_expression(value_str) {
        Ok((_, expr)) => expr,
        Err(_) => {
            // If parsing fails (e.g., plain text), treat as a string literal
            Expr::String(Some(value_str))
        }
    };

    ParseResult::Single(Element::Esi(Tag::Assign { name, value }))
}

fn parse_assign_long<'a>(
    attrs: Vec<(&'a str, &'a str)>,
    content: Vec<Element<'a>>,
) -> ParseResult<'a> {
    let mut name = "";
    for (key, val) in attrs {
        if key == "name" {
            name = val;
        }
    }

    // Per ESI spec, long form value comes from content between tags
    // Content is already parsed as Vec<Element> (can be text, expressions, etc.)
    // We need to convert it to a single expression
    let value = if content.is_empty() {
        // Empty content - empty string
        Expr::String(Some(""))
    } else if content.len() == 1 {
        // Single element - use it directly
        if let Element::Expr(expr) = &content[0] {
            expr.clone()
        } else if let Element::Text(text) = &content[0] {
            // Try to parse the text as an expression
            match parse_expression(text) {
                Ok((_, expr)) => expr,
                Err(_) => Expr::String(Some(text)),
            }
        } else {
            // HTML or other - treat as empty string
            Expr::String(Some(""))
        }
    } else {
        // Multiple elements - this is a compound expression per ESI spec
        // Examples: <esi:assign name="x">prefix$(VAR)suffix</esi:assign>
        //           <esi:assign name="y">$(A) + $(B)</esi:assign>
        // Store the elements as-is for runtime evaluation
        Expr::Interpolated(content)
    };

    ParseResult::Single(Element::Esi(Tag::Assign { name, value }))
}

fn esi_assign_short(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(
        delimited(
            tag("<esi:assign"),
            attributes,
            preceded(multispace0, tag("/>")),
        ),
        parse_assign_attributes_short,
    )(input)
}

fn esi_assign_long(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(
        tuple((
            delimited(
                tag("<esi:assign"),
                attributes,
                preceded(multispace0, tag(">")),
            ),
            parse_interpolated,
            tag("</esi:assign>"),
        )),
        |(attrs, content, _)| parse_assign_long(attrs, content.into_vec()),
    )(input)
}
fn esi_except(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(
        delimited(
            tag("<esi:except>"),
            parse_interpolated,
            tag("</esi:except>"),
        ),
        |v| ParseResult::Single(Element::Esi(Tag::Except(v.into_vec()))),
    )(input)
}
fn esi_attempt(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(
        delimited(
            tag("<esi:attempt>"),
            parse_interpolated,
            tag("</esi:attempt>"),
        ),
        |v| ParseResult::Single(Element::Esi(Tag::Attempt(v.into_vec()))),
    )(input)
}
fn esi_try(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(delimited(tag("<esi:try>"), parse, tag("</esi:try>")), |v| {
        let mut attempts = vec![];
        let mut except = None;
        for element in v.into_vec() {
            match element {
                Element::Esi(Tag::Attempt(cs)) => attempts.push(cs),
                Element::Esi(Tag::Except(cs)) => {
                    except = Some(cs);
                }
                _ => {} // Ignore content outside attempt/except blocks
            }
        }
        ParseResult::Single(Element::Esi(Tag::Try {
            attempt_events: attempts,
            except_events: except.unwrap_or_default(),
        }))
    })(input)
}

fn esi_otherwise(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(
        tuple((
            tag("<esi:otherwise>"),
            parse_interpolated,
            tag("</esi:otherwise>"),
        )),
        |(_, content, _)| {
            // Return the Otherwise tag followed by its content elements (same as esi_when)
            let mut result = vec![Element::Esi(Tag::Otherwise)];
            result.extend(content.into_vec());
            ParseResult::Multiple(result)
        },
    )(input)
}

fn esi_when(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(
        tuple((
            delimited(
                tag("<esi:when"),
                attributes,
                preceded(multispace0, alt((tag(">"), tag("/>")))),
            ),
            parse_interpolated,
            tag("</esi:when>"),
        )),
        |(attrs, content, _)| {
            let test = attrs
                .iter()
                .find(|(key, _)| key.as_bytes() == b"test")
                .map(|(_, val)| *val)
                .unwrap_or("");

            let match_name = attrs
                .iter()
                .find(|(key, _)| key.as_bytes() == b"matchname")
                .map(|(_, val)| val.to_string());

            // Return the When tag followed by its content elements as a marker
            let mut result = vec![Element::Esi(Tag::When { test, match_name })];
            result.extend(content.into_vec());
            ParseResult::Multiple(result)
        },
    )(input)
}

fn esi_choose(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(
        delimited(tag("<esi:choose>"), parse, tag("</esi:choose>")),
        |v| {
            let mut when_branches = vec![];
            let mut otherwise_events = Vec::new();
            let mut current_when: Option<WhenBranch> = None;
            let mut in_otherwise = false;

            for element in v.into_vec() {
                match element {
                    Element::Esi(Tag::When { test, match_name }) => {
                        // Save any previous when
                        if let Some(when_branch) = current_when.take() {
                            when_branches.push(when_branch);
                        }
                        in_otherwise = false;

                        // Parse the test expression now, at parse time (not at eval time)
                        let test_expr = match parse_expression(test) {
                            Ok((_, expr)) => expr,
                            Err(_) => {
                                // If parsing fails, create a simple false expression
                                // This matches the behavior of treating parse failures gracefully
                                Expr::Integer(0)
                            }
                        };

                        // Start collecting for this new when
                        current_when = Some(WhenBranch {
                            test: test_expr,
                            match_name,
                            content: Vec::new(),
                        });
                    }
                    Element::Esi(Tag::Otherwise) => {
                        // Save any pending when
                        if let Some(when_branch) = current_when.take() {
                            when_branches.push(when_branch);
                        }
                        in_otherwise = true;
                    }
                    _ => {
                        // Accumulate content for the current when or otherwise
                        if in_otherwise {
                            otherwise_events.push(element);
                        } else if let Some(ref mut when_branch) = current_when {
                            when_branch.content.push(element);
                        }
                        // Content outside when/otherwise blocks is discarded (per ESI spec)
                    }
                }
            }

            // Don't forget the last when if there is one
            if let Some(when_branch) = current_when {
                when_branches.push(when_branch);
            }

            ParseResult::Single(Element::Esi(Tag::Choose {
                when_branches,
                otherwise_events,
            }))
        },
    )(input)
}

// Note: <esi:vars> does NOT create a Tag::Vars element. Instead, it parses the content
// (either the body of <esi:vars>...</esi:vars> or the name attribute of <esi:vars name="..."/>)
// and returns the evaluated content directly as ParseResult. These elements (Text, Expr, Html, etc.)
// are then flattened into the main element stream and processed normally by process_elements() in lib.rs.
fn esi_vars(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    alt((esi_vars_short, esi_vars_long))(input)
}

fn parse_vars_attributes<'a>(
    attrs: Vec<(&'a str, &'a str)>,
) -> Result<ParseResult<'a>, &'static str> {
    if let Some((_k, v)) = attrs.iter().find(|(k, _v)| *k == "name") {
        if let Ok((_, result)) = expression(v) {
            Ok(result)
        } else {
            Err("failed to parse expression")
        }
    } else {
        Err("no name field in short form vars")
    }
}

fn esi_vars_short(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map_res(
        delimited(
            tag("<esi:vars"),
            attributes,
            preceded(multispace0, tag("/>")), // Short form must be self-closing per ESI spec
        ),
        parse_vars_attributes,
    )(input)
}

// Parser for ESI tags that can appear inside vars (everything except vars itself to avoid recursion)
fn esi_tag_non_vars(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    alt((
        esi_assign,
        esi_include,
        // esi_vars,  // Excluded to prevent infinite recursion
        esi_comment,
        esi_remove,
        esi_text,
        esi_choose,
        esi_try,
        esi_when,
        esi_otherwise,
        esi_attempt,
        esi_except,
    ))(input)
}

// Parser for content inside esi:vars - handles text, expressions, and most ESI tags (except nested vars)
// Supports nested variable expressions like $(VAR{$(other)}) as of the nom migration
fn parse_vars_content(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(
        many0(alt((
            interpolated_text,
            interpolated_expression,
            esi_tag_non_vars,
            html,
        ))),
        ParseResult::from_results,
    )(input)
}

fn esi_vars_long(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    // Use parse_vars_content instead of parse_interpolated to avoid infinite recursion
    delimited(tag("<esi:vars>"), parse_vars_content, tag("</esi:vars>"))(input)
}

fn esi_comment(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(
        delimited(
            tag("<esi:comment"),
            attributes,
            preceded(multispace0, alt((tag(">"), tag("/>")))),
        ),
        |_| ParseResult::Empty,
    )(input)
}
fn esi_remove(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(
        delimited(tag("<esi:remove>"), parse, tag("</esi:remove>")),
        |_| ParseResult::Empty,
    )(input)
}

fn esi_text(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(
        delimited(
            tag("<esi:text>"),
            take_until("</esi:text>"),
            tag("</esi:text>"),
        ),
        |v| ParseResult::Single(Element::Text(v)),
    )(input)
}
fn esi_include(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(
        delimited(
            tag("<esi:include"),
            attributes,
            preceded(multispace0, alt((tag(">"), tag("/>")))),
        ),
        |attrs| {
            let mut src = "";
            let mut alt = None;
            let mut continue_on_error = false;
            for (key, val) in attrs {
                match key.as_bytes() {
                    b"src" => src = val,
                    b"alt" => alt = Some(val),
                    b"onerror" => continue_on_error = val.as_bytes() == b"continue",
                    _ => {}
                }
            }
            ParseResult::Single(Element::Esi(Tag::Include {
                src,
                alt,
                continue_on_error,
            }))
        },
    )(input)
}

fn attributes(input: &str) -> IResult<&str, Vec<(&str, &str)>, Error<&str>> {
    many0(separated_pair(
        preceded(multispace1, alpha1),
        char('='),
        htmlstring,
    ))(input)
}

fn htmlstring(input: &str) -> IResult<&str, &str, Error<&str>> {
    delimited(char('"'), take_while1(|c| c != '"'), char('"'))(input)
}

fn html(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    alt((html_comment, script, end_tag, start_tag))(input)
}

fn html_comment(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(
        recognize(delimited(tag("<!--"), take_until("-->"), tag("-->"))),
        |s: &str| ParseResult::Single(Element::Html(s)),
    )(input)
}

/// Fast case-insensitive take_until for </script
fn take_until_close_script(input: &str) -> IResult<&str, &str, Error<&str>> {
    let bytes = input.as_bytes();
    let pattern = b"</script";

    for i in 0..bytes.len().saturating_sub(pattern.len()) {
        let window = &bytes[i..i + pattern.len()];
        if window.eq_ignore_ascii_case(pattern) {
            return Ok((&input[i..], &input[0..i]));
        }
    }

    Err(nom::Err::Error(Error::new(
        input,
        nom::error::ErrorKind::TakeUntil,
    )))
}

fn script(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(
        tuple((
            recognize(verify(
                delimited(tag_no_case("<script"), attributes, char('>')),
                |attrs: &Vec<(&str, &str)>| !attrs.iter().any(|(k, _)| k == &"src"),
            )),
            take_until_close_script,
            recognize(delimited(
                tag_no_case("</script"),
                take_while(|c| c != '>'),
                char('>'),
            )),
        )),
        |(start, script, end)| {
            ParseResult::Multiple(vec![
                Element::Html(start),
                Element::Text(script),
                Element::Html(end),
            ])
        },
    )(input)
}

fn end_tag(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(
        verify(
            recognize(delimited(tag("</"), is_not(">"), char('>'))),
            |s: &str| !s.starts_with("</esi:"),
        ),
        |s: &str| ParseResult::Single(Element::Html(s)),
    )(input)
}

fn start_tag(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(
        verify(
            recognize(delimited(char('<'), is_not(">"), char('>'))),
            |s: &str| !s.starts_with("</") && !s.starts_with("<esi:"),
        ),
        |s: &str| ParseResult::Single(Element::Html(s)),
    )(input)
}
fn text(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(take_while1(|c| c != '<'), |s: &str| {
        ParseResult::Single(Element::Text(s))
    })(input)
}
fn interpolated_text(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(take_while1(|c| c != '<' && c != '$'), |s: &str| {
        ParseResult::Single(Element::Text(s))
    })(input)
}

fn is_alphanumeric_or_underscore(c: char) -> bool {
    c.is_alphanum() || c == '_'
}

fn is_lower_alphanumeric_or_underscore(c: char) -> bool {
    c.is_ascii_lowercase() || c.is_numeric() || c == '_'
}

fn fn_name(input: &str) -> IResult<&str, &str, Error<&str>> {
    preceded(char('$'), take_while1(is_lower_alphanumeric_or_underscore))(input)
}

fn var_name(input: &str) -> IResult<&str, Expr<'_>, Error<&str>> {
    map(
        tuple((
            take_while1(is_alphanumeric_or_underscore),
            opt(delimited(char('{'), var_key_expr, char('}'))),
            opt(preceded(char('|'), fn_nested_argument)),
        )),
        |(name, key, default)| Expr::Variable(name, key.map(Box::new), default.map(Box::new)),
    )(input)
}

fn not_dollar_or_curlies(input: &str) -> IResult<&str, &str, Error<&str>> {
    take_till(|c: char| "${},\"".contains(c))(input)
}

// TODO: handle escaping
fn single_quoted_string(input: &str) -> IResult<&str, &str, Error<&str>> {
    delimited(
        char('\''),
        take_till(|c: char| c == '\'' || !c.is_ascii()),
        char('\''),
    )(input)
}
fn triple_quoted_string(input: &str) -> IResult<&str, &str, Error<&str>> {
    delimited(tag("'''"), take_until("'''"), tag("'''"))(input)
}

fn string(input: &str) -> IResult<&str, Expr<'_>, Error<&str>> {
    map(
        alt((single_quoted_string, triple_quoted_string)),
        |string| {
            if string.is_empty() {
                Expr::String(None)
            } else {
                Expr::String(Some(string))
            }
        },
    )(input)
}

fn var_key(input: &str) -> IResult<&str, &str, Error<&str>> {
    alt((
        single_quoted_string,
        triple_quoted_string,
        not_dollar_or_curlies,
    ))(input)
}

// Parse subscript key - can be a string or a nested variable expression
fn var_key_expr(input: &str) -> IResult<&str, Expr<'_>, Error<&str>> {
    alt((
        // Try to parse as a variable first (e.g., $(keyVar))
        variable,
        // Otherwise parse as a string
        map(var_key, |s| Expr::String(Some(s))),
    ))(input)
}

fn fn_argument(input: &str) -> IResult<&str, Vec<Expr<'_>>, Error<&str>> {
    let (input, mut parsed) = separated_list0(
        tuple((multispace0, char(','), multispace0)),
        fn_nested_argument,
    )(input)?;

    // If the parsed list contains a single empty string element return an empty vec
    if parsed.len() == 1 && parsed[0] == Expr::String(None) {
        parsed = vec![];
    }
    Ok((input, parsed))
}

fn fn_nested_argument(input: &str) -> IResult<&str, Expr<'_>, Error<&str>> {
    alt((call, variable, string, integer, bareword))(input)
}

fn integer(input: &str) -> IResult<&str, Expr<'_>, Error<&str>> {
    map_res(
        recognize(tuple((
            opt(char('-')),
            take_while1(|c: char| c.is_ascii_digit()),
        ))),
        |s: &str| s.parse::<i32>().map(Expr::Integer),
    )(input)
}

fn bareword(input: &str) -> IResult<&str, Expr<'_>, Error<&str>> {
    map(take_while1(is_alphanumeric_or_underscore), |name: &str| {
        Expr::Variable(name, None, None)
    })(input)
}

fn call(input: &str) -> IResult<&str, Expr<'_>, Error<&str>> {
    let (input, parsed) = tuple((
        fn_name,
        delimited(
            terminated(char('('), multispace0),
            fn_argument,
            preceded(multispace0, char(')')),
        ),
    ))(input)?;

    let (name, args) = parsed;

    Ok((input, Expr::Call(name, args)))
}

fn variable(input: &str) -> IResult<&str, Expr<'_>, Error<&str>> {
    delimited(tag("$("), var_name, char(')'))(input)
}

fn operator(input: &str) -> IResult<&str, Operator, Error<&str>> {
    alt((
        // Try longer operators first
        map(tag("matches_i"), |_| Operator::MatchesInsensitive),
        map(tag("matches"), |_| Operator::Matches),
        map(tag("=="), |_| Operator::Equals),
        map(tag("!="), |_| Operator::NotEquals),
        map(tag("<="), |_| Operator::LessThanOrEqual),
        map(tag(">="), |_| Operator::GreaterThanOrEqual),
        map(tag("<"), |_| Operator::LessThan),
        map(tag(">"), |_| Operator::GreaterThan),
        map(tag("&&"), |_| Operator::And),
        map(tag("||"), |_| Operator::Or),
    ))(input)
}

fn interpolated_expression(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(alt((call, variable)), |expr| {
        ParseResult::Single(Element::Expr(expr))
    })(input)
}

fn primary_expr(input: &str) -> IResult<&str, Expr<'_>, Error<&str>> {
    alt((
        // Parse negation: !expr
        map(
            preceded(char('!'), preceded(multispace0, primary_expr)),
            |expr| Expr::Not(Box::new(expr)),
        ),
        // Parse grouped expression: (expr)
        delimited(
            char('('),
            delimited(multispace0, expr, multispace0),
            char(')'),
        ),
        // Parse basic expressions
        call,
        variable,
        integer,
        string,
    ))(input)
}

fn expr(input: &str) -> IResult<&str, Expr<'_>, Error<&str>> {
    let (rest, exp) = primary_expr(input)?;

    if let Ok((rest, (operator, right_exp))) =
        tuple((delimited(multispace0, operator, multispace0), expr))(rest)
    {
        Ok((
            rest,
            Expr::Comparison {
                left: Box::new(exp),
                operator,
                right: Box::new(right_exp),
            },
        ))
    } else {
        Ok((rest, exp))
    }
}
fn expression(input: &str) -> IResult<&str, ParseResult<'_>, Error<&str>> {
    map(expr, |x| ParseResult::Single(Element::Expr(x)))(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_parse() {
        let input = r#"
<a>foo</a>
<bar />
baz
<esi:vars name="$(hello)"/>
<esi:vars>
hello <br>
</esi:vars>
<sCripT src="whatever">
<baz>
<script> less < more </script>
<esi:remove>should not appear</esi:remove>
<esi:comment text="also should not appear" />
<esi:text> this <esi:vars>$(should)</esi> appear unchanged</esi:text>
<esi:include src="whatever" />
<esi:choose>
should not appear
</esi:choose>
<esi:choose>
should not appear
<esi:when test="whatever">hi</esi:when>
<esi:otherwise>goodbye</esi:otherwise>
should not appear
</esi:choose>
<esi:try>
should not appear
<esi:attempt>
attempt 1
</esi:attempt>
should not appear
<esi:attempt>
attempt 2
</esi:attempt>
should not appear
<esi:except>
exception!
</esi:except>
</esi:try>"#;
        let result = parse(input);
        match result {
            Ok((rest, _)) => {
                // Just test to make sure it parsed the whole thing
                if !rest.is_empty() {
                    panic!("Failed to parse completely. Remaining: '{}'", rest);
                }
            }
            Err(e) => {
                panic!("Parse failed with error: {:?}", e);
            }
        }
    }
    #[test]
    fn test_new_parse_script() {
        let (rest, x) = script("<sCripT> less < more </scRIpt>").unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(
            x.into_vec(),
            [
                Element::Html("<sCripT>"),
                Element::Text(" less < more "),
                Element::Html("</scRIpt>")
            ]
        );
    }
    #[test]
    fn test_new_parse_script_with_src() {
        let (rest, x) = parse("<sCripT src=\"whatever\">").unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(x.into_vec(), [Element::Html("<sCripT src=\"whatever\">")]);
    }
    #[test]
    fn test_new_parse_esi_vars_short() {
        let (rest, x) = esi_tag(r#"<esi:vars name="$(hello)"/>"#).unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(
            x.into_vec(),
            [Element::Expr(Expr::Variable("hello", None, None)),]
        );
    }
    #[test]
    fn test_new_parse_esi_vars_long() {
        // Nested <esi:vars> tags are not supported to prevent infinite recursion
        // The inner <esi:vars> tags should be treated as plain text/HTML
        let (rest, x) = parse(r#"<esi:vars>hello<br></esi:vars>"#).unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(
            x.into_vec(),
            [Element::Text("hello"), Element::Html("<br>"),]
        );
    }

    #[test]
    fn test_nested_vars_not_supported() {
        // This test documents that nested <esi:vars> are explicitly NOT supported
        // The inner <esi:vars> tag will be treated as text
        let input = r#"<esi:vars>outer<esi:vars>inner</esi:vars></esi:vars>"#;
        let result = parse(input);

        // The parser should either:
        // 1. Fail to parse completely (leaving remainder), OR
        // 2. Parse the outer vars but treat inner vars as text
        match result {
            Ok((rest, elements)) => {
                // If it parses, check that we either have remaining input
                // or the inner <esi:vars> is treated as text
                if rest.is_empty() {
                    // Inner vars should be treated as text/HTML
                    eprintln!("Parsed elements: {:?}", elements);
                    let elements_vec = elements.into_vec();
                    // We expect the text "outer<esi:vars>inner" to be captured somehow
                    assert!(
                        elements_vec
                            .iter()
                            .any(|c| matches!(c, Element::Text(t) if t.contains("inner"))),
                        "Inner <esi:vars> content should be present as text"
                    );
                } else {
                    // Parser stopped early - this is acceptable behavior
                    eprintln!("Parser stopped with remaining: {:?}", rest);
                    assert!(
                        rest.contains("<esi:vars>"),
                        "Remaining should include the problematic nested vars"
                    );
                }
            }
            Err(e) => {
                eprintln!("Parser error (expected): {:?}", e);
                // Parsing error is also acceptable
            }
        }
    }
    #[test]
    fn test_new_parse_complex_expr() {
        let (rest, x) =
            parse(r#"<esi:vars name="$call('hello') matches $(var{'key'})"/>"#).unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(
            x.into_vec(),
            [Element::Expr(Expr::Comparison {
                left: Box::new(Expr::Call("call", vec![Expr::String(Some("hello"))])),
                operator: Operator::Matches,
                right: Box::new(Expr::Variable(
                    "var",
                    Some(Box::new(Expr::String(Some("key")))),
                    None
                ))
            })]
        );
    }

    #[test]
    fn test_vars_with_content() {
        let input = r#"<esi:vars>
            $(QUERY_STRING{param})
        </esi:vars>"#;
        let result = esi_vars_long(input);
        assert!(
            result.is_ok(),
            "esi_vars_long should parse successfully: {:?}",
            result.err()
        );
        let (rest, _elements) = result.unwrap();
        assert_eq!(
            rest.len(),
            0,
            "Parser should consume all input. Remaining: '{}'",
            rest
        );
    }

    #[test]
    fn test_exact_failing_input() {
        // This is the exact input from the failing test
        let input = r#"
        <esi:assign name="keyVar" value="'param'" />
        <esi:vars>
            $(QUERY_STRING{param})
            $(QUERY_STRING{$(keyVar)})
        </esi:vars>
    "#;
        let (rest, elements) = parse(input).unwrap();
        eprintln!("Chunks: {:?}", elements);
        eprintln!("Remaining: {:?}", rest);
        assert_eq!(
            rest.len(),
            0,
            "Parser should consume all input. Remaining: '{}'",
            rest
        );
    }

    #[test]
    fn test_esi_vars_directly() {
        let input = r#"<esi:vars>
            $(QUERY_STRING{param})
            $(QUERY_STRING{$(keyVar)})
        </esi:vars>"#;
        eprintln!("Testing esi_vars on input: {:?}", input);
        let result = esi_vars(input);
        eprintln!("Result: {:?}", result);
        assert!(result.is_ok(), "esi_vars should parse: {:?}", result.err());
    }

    #[test]
    fn test_esi_tag_on_vars() {
        let input = r#"<esi:vars>
            $(QUERY_STRING{param})
        </esi:vars>"#;
        eprintln!("Testing esi_tag on input: {:?}", input);
        let result = esi_tag(input);
        eprintln!("Result: {:?}", result);
        assert!(result.is_ok(), "esi_tag should parse: {:?}", result.err());
    }

    #[test]
    fn test_assign_then_vars() {
        // Test simple case without nested variables (which aren't supported yet)
        let input =
            r#"<esi:assign name="key" value="'val'" /><esi:vars>$(QUERY_STRING{param})</esi:vars>"#;
        let (rest, _elements) = parse(input).unwrap();
        assert_eq!(rest.len(), 0);
    }

    #[test]
    fn test_new_parse_plain_text() {
        let (rest, x) = parse("hello\nthere").unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(x.into_vec(), [Element::Text("hello\nthere")]);
    }
    #[test]
    fn test_new_parse_interpolated() {
        let (rest, x) = parse("hello $(foo)<esi:vars>goodbye $(foo)</esi:vars>").unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(
            x.into_vec(),
            [
                Element::Text("hello $(foo)"),
                Element::Text("goodbye "),
                Element::Expr(Expr::Variable("foo", None, None)),
            ]
        );
    }
    #[test]
    fn test_new_parse_examples() {
        let (rest, _) = parse(include_str!(
            "../../examples/esi_vars_example/src/index.html"
        ))
        .unwrap();
        // just make sure it parsed the whole thing
        assert_eq!(rest.len(), 0);
    }

    #[test]
    fn test_parse_equality_operators() {
        let input = r#"$(foo) == 'bar'"#;
        let (rest, result) = expr(input).unwrap();
        assert_eq!(rest.len(), 0);
        assert!(matches!(
            result,
            Expr::Comparison {
                operator: Operator::Equals,
                ..
            }
        ));

        let input2 = r#"$(foo) != 'bar'"#;
        let (rest, result) = expr(input2).unwrap();
        assert_eq!(rest.len(), 0);
        assert!(matches!(
            result,
            Expr::Comparison {
                operator: Operator::NotEquals,
                ..
            }
        ));
    }

    #[test]
    fn test_parse_comparison_operators() {
        let input = r#"$(count) < 10"#;
        let (rest, result) = expr(input).unwrap();
        assert_eq!(rest.len(), 0);
        assert!(matches!(
            result,
            Expr::Comparison {
                operator: Operator::LessThan,
                ..
            }
        ));

        let input2 = r#"$(count) >= 5"#;
        let (rest, result) = expr(input2).unwrap();
        assert_eq!(rest.len(), 0);
        assert!(matches!(
            result,
            Expr::Comparison {
                operator: Operator::GreaterThanOrEqual,
                ..
            }
        ));
    }

    #[test]
    fn test_parse_logical_operators() {
        // With parentheses to enforce correct precedence
        let input = r#"($(foo) == 'bar') && ($(baz) == 'qux')"#;
        let (rest, result) = expr(input).unwrap();
        assert_eq!(rest.len(), 0);
        assert!(matches!(
            result,
            Expr::Comparison {
                operator: Operator::And,
                ..
            }
        ));

        let input2 = r#"($(foo) == 'bar') || ($(baz) == 'qux')"#;
        let (rest, result) = expr(input2).unwrap();
        assert_eq!(rest.len(), 0);
        assert!(matches!(
            result,
            Expr::Comparison {
                operator: Operator::Or,
                ..
            }
        ));
    }

    #[test]
    fn test_parse_negation() {
        let input = r#"!$(flag)"#;
        let (rest, result) = expr(input).unwrap();
        assert_eq!(rest.len(), 0);
        assert!(matches!(result, Expr::Not(_)));

        // Test negation with comparison
        let input2 = r#"!($(foo) == 'bar')"#;
        let (rest, result) = expr(input2).unwrap();
        assert_eq!(rest.len(), 0);
        assert!(matches!(result, Expr::Not(_)));
    }

    #[test]
    fn test_parse_grouped_expressions() {
        let input = r#"($(foo) == 'bar')"#;
        let (rest, result) = expr(input).unwrap();
        assert_eq!(rest.len(), 0);
        assert!(matches!(
            result,
            Expr::Comparison {
                operator: Operator::Equals,
                ..
            }
        ));
    }

    #[test]
    fn test_html_comment() {
        let input = "<!-- this is a comment -->";
        let result = html_comment(input);
        assert!(result.is_ok(), "Failed to parse HTML comment: {:?}", result);
        let (rest, result) = result.unwrap();
        assert_eq!(rest, "");
        let elements = result.into_vec();
        assert_eq!(elements.len(), 1);
        match &elements[0] {
            Element::Html(s) => assert_eq!(*s, "<!-- this is a comment -->"),
            _ => panic!("Expected Html element"),
        }
    }

    #[test]
    fn test_html_comment_in_document() {
        let input = "<!-- comment --><div>test</div>";
        let (rest, result) = parse(input).unwrap();
        assert_eq!(rest, "");
        let elements = result.into_vec();
        // Comment should be parsed as one element
        assert!(elements.len() >= 1, "Expected at least 1 element");
        match &elements[0] {
            Element::Html(s) => assert_eq!(*s, "<!-- comment -->"),
            _ => panic!("Expected Html element for comment, got {:?}", &elements[0]),
        }
    }
}
