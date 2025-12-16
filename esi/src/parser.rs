use bytes::Bytes;
use nom::branch::alt;
// Using STREAMING parsers for document structure - they return Incomplete when they need more data
// This enables TRUE bounded-memory streaming for the main document parsing
use nom::bytes::streaming::{
    tag, tag_no_case, take_till, take_until, take_while, take_while1, take_while_m_n,
};
use nom::character::streaming::{alpha1, multispace0, multispace1};
// Using COMPLETE parsers for expression parsing - expressions are always complete
// (they come from attribute values which are fully extracted before parsing)
use nom::bytes::complete as complete_bytes;
use nom::character::complete as complete_char;
use nom::combinator::{map, map_res, not, opt, peek, recognize};
use nom::error::Error;
use nom::multi::{fold_many0, separated_list0};
use nom::sequence::{delimited, preceded, separated_pair, terminated, tuple};
use nom::IResult;
use std::collections::HashMap;

use crate::parser_types::*;

// ============================================================================
// Zero-Copy Helpers
// ============================================================================

/// View a slice from nom parsing as a Bytes reference
/// This enables zero-copy: we calculate the slice's offset within the original
/// Bytes and return a new Bytes that references the same underlying data (just increments ref count)
#[inline]
fn slice_as_bytes(original: &Bytes, slice: &[u8]) -> Bytes {
    // Calculate the offset of the slice within the original Bytes
    let original_ptr = original.as_ptr() as usize;
    let slice_ptr = slice.as_ptr() as usize;

    // Safety check: slice must be within original's memory range
    debug_assert!(
        slice_ptr >= original_ptr && slice_ptr + slice.len() <= original_ptr + original.len(),
        "slice must be within original Bytes range"
    );

    let offset = slice_ptr - original_ptr;
    let len = slice.len();

    // Zero-copy: slice the original Bytes (just increments refcount)
    original.slice(offset..offset + len)
}

/// Helper for parsing loops that accumulate results
/// Handles the common pattern of calling a parser in a loop and accumulating elements
enum ParsingMode {
    /// Return Incomplete if no elements parsed yet, otherwise return accumulated results
    Streaming,
    /// Treat Incomplete as EOF, convert remaining bytes to Text
    Complete,
}

/// Parser output that avoids Vec allocation for single elements
/// This is a key optimization: most parsers return exactly one element,
/// so we avoid the Vec allocation overhead in the common case.
enum ParseResult {
    /// Single element (most common case - no Vec allocation)
    Single(Element),
    /// Multiple elements (for parsers that return variable number of elements)
    Multiple(Vec<Element>),
    /// No elements (for esi:comment, esi:remove that produce nothing)
    Empty,
}

impl ParseResult {
    /// Append elements to an existing Vec
    #[inline]
    fn append_to(self, acc: &mut Vec<Element>) {
        match self {
            ParseResult::Single(e) => acc.push(e),
            ParseResult::Multiple(mut v) => acc.append(&mut v),
            ParseResult::Empty => {}
        }
    }
}

/// Zero-copy parse loop that threads Bytes through the parser chain
fn parse_loop<'a, F>(
    original: &Bytes,
    input: &'a [u8],
    mut parser: F,
    incomplete_strategy: ParsingMode,
) -> IResult<&'a [u8], Vec<Element>, Error<&'a [u8]>>
where
    F: FnMut(&Bytes, &'a [u8]) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>>,
{
    let mut result = Vec::new();
    let mut remaining = input;

    loop {
        match parser(original, remaining) {
            Ok((rest, parse_result)) => {
                parse_result.append_to(&mut result);

                // If we consumed nothing, break to avoid infinite loop
                if rest.len() == remaining.len() {
                    return Ok((rest, result));
                }
                remaining = rest;
            }
            Err(nom::Err::Incomplete(needed)) => {
                return match incomplete_strategy {
                    ParsingMode::Streaming => {
                        // Return accumulated results or propagate Incomplete
                        if result.is_empty() {
                            Err(nom::Err::Incomplete(needed))
                        } else {
                            Ok((remaining, result))
                        }
                    }
                    ParsingMode::Complete => {
                        // Treat remaining bytes as text - ZERO COPY!
                        if !remaining.is_empty() {
                            result.push(Element::Text(slice_as_bytes(original, remaining)));
                            Ok((&remaining[remaining.len()..], result))
                        } else {
                            Ok((remaining, result))
                        }
                    }
                };
            }
            Err(e) => {
                // Real parse error
                if result.is_empty() {
                    return Err(e);
                } else {
                    return Ok((remaining, result));
                }
            }
        }
    }
}

// ============================================================================
// Public APIs - Zero-Copy Streaming Parsers
// ============================================================================

/// Parse input bytes into ESI elements using TRUE STREAMING parsers
/// Returns Incomplete when more data is needed - this is proper streaming behavior
/// lib.rs must handle Incomplete by reading more data into the buffer
/// ZERO-COPY: Returns Bytes slices that reference the original buffer (no copying!)
pub fn parse(input: &Bytes) -> IResult<&[u8], Vec<Element>, Error<&[u8]>> {
    parse_loop(input, input.as_ref(), element, ParsingMode::Streaming)
}

/// Parse complete document (treats Incomplete as EOF and converts to text)
/// Wrapper for complete input (tests) - treats Incomplete as "done parsing"
/// ZERO-COPY: Returns Bytes slices that reference the original buffer (no copying!)
pub fn parse_complete(input: &Bytes) -> IResult<&[u8], Vec<Element>, Error<&[u8]>> {
    parse_loop(input, input.as_ref(), element, ParsingMode::Complete)
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Convert bytes to String using lossy UTF-8 conversion
#[inline]
fn bytes_to_string(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

// ============================================================================
// Expression Parsing - Uses COMPLETE parsers (input is always complete)
// Expressions come from attribute values which are fully extracted before parsing
// ============================================================================

/// Accepts str for convenience but works on bytes internally
pub fn parse_expression(input: &str) -> IResult<&str, Expr, Error<&str>> {
    let bytes = input.as_bytes();
    match expr(bytes) {
        Ok((remaining_bytes, expr)) => {
            let consumed = bytes.len() - remaining_bytes.len();
            Ok((&input[consumed..], expr))
        }
        Err(nom::Err::Error(e)) => Err(nom::Err::Error(Error::new(input, e.code))),
        Err(nom::Err::Failure(e)) => Err(nom::Err::Failure(Error::new(input, e.code))),
        Err(nom::Err::Incomplete(_)) => {
            // Complete parsers should never return Incomplete
            unreachable!("complete parsers don't return Incomplete")
        }
    }
}

/// Parses a string that may contain interpolated expressions like $(VAR)
/// ZERO-COPY: Accepts &Bytes and returns Bytes slices that reference the original
pub fn parse_interpolated_string(input: &Bytes) -> IResult<&[u8], Vec<Element>, Error<&[u8]>> {
    // NOTE: This function parses complete strings (like attribute values), not streaming input
    // So we need to manually accumulate results and handle Incomplete as EOF
    let bytes = input.as_ref();
    let mut result = Vec::new();
    let mut remaining = bytes;

    loop {
        match alt((interpolated_expression, |i| interpolated_text(input, i)))(remaining) {
            Ok((rest, parse_result)) => {
                parse_result.append_to(&mut result);
                if rest.is_empty() {
                    // Parsed everything
                    return Ok((b"", result));
                }
                remaining = rest;
            }
            Err(nom::Err::Incomplete(_)) => {
                // Streaming parser needs more data, but we have complete input
                // If we haven't consumed anything yet and have input, treat it all as text - ZERO COPY!
                if result.is_empty() && !remaining.is_empty() {
                    result.push(Element::Text(slice_as_bytes(input, remaining)));
                    return Ok((b"", result));
                }
                // Otherwise we've parsed what we can
                return Ok((remaining, result));
            }
            Err(e) => {
                // Real parse error - propagate it
                return Err(e);
            }
        }
    }
}

/// Zero-copy element parser - dispatches to text or tag_dispatch
fn element<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    alt((|i| text(original, i), |i| tag_handler(original, i)))(input)
}

fn parse_interpolated<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], Vec<Element>, Error<&'a [u8]>> {
    fold_many0(
        |i| interpolated_element(original, i),
        Vec::new,
        |mut acc: Vec<Element>, item: ParseResult| {
            item.append_to(&mut acc);
            acc
        },
    )(input)
}

fn interpolated_element<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    alt((
        |i| interpolated_text(original, i),
        interpolated_expression,
        // |i| esi_tag(original, i),
        |i| tag_handler(original, i),
    ))(input)
}

fn esi_assign<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    alt((esi_assign_short, |i| esi_assign_long(original, i)))(input)
}

fn assign_attributes_short(attrs: HashMap<String, String>) -> ParseResult {
    let name = attrs.get("name").cloned().unwrap_or_default();
    let value_str = attrs.get("value").cloned().unwrap_or_default();

    // Per ESI spec, short form value attribute contains an expression
    // Try to parse as ESI expression. If it fails, treat as string literal.
    let value = match parse_expression(&value_str) {
        Ok((_, expr)) => expr,
        Err(_) => {
            // If parsing fails (e.g., plain text), treat as a string literal
            Expr::String(Some(value_str))
        }
    };

    ParseResult::Single(Element::Esi(Tag::Assign { name, value }))
}

fn assign_long(attrs: HashMap<String, String>, mut content: Vec<Element>) -> ParseResult {
    let name = attrs.get("name").cloned().unwrap_or_default();

    // Per ESI spec, long form value comes from content between tags
    // Content is already parsed as Vec<Element> (can be text, expressions, etc.)
    // We need to convert it to a single expression
    let value = if content.is_empty() {
        // Empty content - empty string
        Expr::String(Some(String::new()))
    } else if content.len() == 1 {
        // Single element - pop to take ownership
        match content.pop().expect("checked len == 1") {
            Element::Expr(expr) => expr,
            Element::Text(text) => {
                // Try to parse the text as an expression
                let text_str = String::from_utf8_lossy(text.as_ref()).to_string();
                match parse_expression(&text_str) {
                    Ok((_, expr)) => expr,
                    Err(_) => Expr::String(Some(text_str)),
                }
            }
            _ => {
                // HTML or other - treat as empty string
                Expr::String(Some(String::new()))
            }
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

fn esi_assign_short(input: &[u8]) -> IResult<&[u8], ParseResult, Error<&[u8]>> {
    map(
        delimited(
            tag(b"<esi:assign"),
            attributes,
            preceded(multispace0, self_closing),
        ),
        assign_attributes_short,
    )(input)
}

fn esi_assign_long<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    map(
        tuple((
            delimited(
                tag(b"<esi:assign"),
                attributes,
                preceded(multispace0, closing_bracket),
            ),
            |i| parse_interpolated(original, i),
            tag(b"</esi:assign>"),
        )),
        |(attrs, content, _)| assign_long(attrs, content),
    )(input)
}

fn esi_except<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    map(
        delimited(
            tag(b"<esi:except>"),
            |i| parse_interpolated(original, i),
            tag(b"</esi:except>"),
        ),
        |v| ParseResult::Single(Element::Esi(Tag::Except(v))),
    )(input)
}

fn esi_attempt<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    map(
        delimited(
            tag(b"<esi:attempt>"),
            |i| parse_interpolated(original, i),
            tag(b"</esi:attempt>"),
        ),
        |v| ParseResult::Single(Element::Esi(Tag::Attempt(v))),
    )(input)
}

// Zero-copy version used by both esi_tag and esi_tag_old (via parse_interpolated)
fn esi_try<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    let (input, _) = tag(b"<esi:try>")(input)?;
    let (input, v) = parse_interpolated(original, input)?;
    let (input, _) = tag(b"</esi:try>")(input)?;

    let mut attempts = vec![];
    let mut except = None;
    for element in v {
        match element {
            Element::Esi(Tag::Attempt(cs)) => attempts.push(cs),
            Element::Esi(Tag::Except(cs)) => {
                except = Some(cs);
            }
            _ => {} // Ignore content outside attempt/except blocks
        }
    }
    Ok((
        input,
        ParseResult::Single(Element::Esi(Tag::Try {
            attempt_events: attempts,
            except_events: except.unwrap_or_default(),
        })),
    ))
}

fn esi_otherwise<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    map(
        delimited(
            tag(b"<esi:otherwise>"),
            |i| parse_interpolated(original, i),
            tag(b"</esi:otherwise>"),
        ),
        |content| {
            // Return the Otherwise tag followed by its content elements
            let mut result = vec![Element::Esi(Tag::Otherwise)];
            result.extend(content);
            ParseResult::Multiple(result)
        },
    )(input)
}

fn esi_when<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    map(
        tuple((
            delimited(
                tag(b"<esi:when"),
                attributes,
                preceded(multispace0, alt((closing_bracket, self_closing))),
            ),
            |i| parse_interpolated(original, i),
            tag(b"</esi:when>"),
        )),
        |(attrs, content, _)| {
            let test = attrs.get("test").cloned().unwrap_or_default();
            let match_name = attrs.get("matchname").cloned();

            // Return the When tag followed by its content elements as a marker
            let mut result = vec![Element::Esi(Tag::When { test, match_name })];
            result.extend(content);
            ParseResult::Multiple(result)
        },
    )(input)
}

/// Zero-copy parser for <esi:choose>...</esi:choose>
fn esi_choose<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    let (input, _) = tag(b"<esi:choose>")(input)?;
    let (input, v) = parse_interpolated(original, input)?;
    let (input, _) = tag(b"</esi:choose>")(input)?;

    let mut when_branches = vec![];
    let mut otherwise_events = Vec::new();
    let mut current_when: Option<WhenBranch> = None;
    let mut in_otherwise = false;

    for element in v {
        match element {
            Element::Esi(Tag::When { test, match_name }) => {
                // Save any previous when
                if let Some(when_branch) = current_when.take() {
                    when_branches.push(when_branch);
                }
                in_otherwise = false;

                // Parse the test expression now, at parse time (not at eval time)
                let test_expr = match parse_expression(&test) {
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

    Ok((
        input,
        ParseResult::Single(Element::Esi(Tag::Choose {
            when_branches,
            otherwise_events,
        })),
    ))
}

// Note: <esi:vars> does NOT create a Tag::Vars element. Instead, it parses the content
// (either the body of <esi:vars>...</esi:vars> or the name attribute of <esi:vars name="..."/>)
// and returns the evaluated content directly as Vec<Element>. These elements (Text, Expr, Html, etc.)
// are then flattened into the main element stream and processed normally by process_elements() in lib.rs.
fn esi_vars<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    alt((esi_vars_short, |i| esi_vars_long(original, i)))(input)
}

fn parse_vars_attributes(attrs: HashMap<String, String>) -> Result<ParseResult, &'static str> {
    if let Some(v) = attrs.get("name") {
        if let Ok((_, expr)) = expression(v.as_bytes()) {
            Ok(ParseResult::Multiple(expr))
        } else {
            Err("failed to parse expression")
        }
    } else {
        Err("no name field in short form vars")
    }
}

fn esi_vars_short(input: &[u8]) -> IResult<&[u8], ParseResult, Error<&[u8]>> {
    map_res(
        delimited(
            tag(b"<esi:vars"),
            attributes,
            preceded(multispace0, self_closing), // Short form must be self-closing per ESI spec
        ),
        parse_vars_attributes,
    )(input)
}

// Parser for content inside esi:vars - handles text, expressions, and ESI tags
// NOTE: Supports nested variable expressions like $(VAR{$(other)})
fn esi_vars_content<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], Vec<Element>, Error<&'a [u8]>> {
    fold_many0(
        alt((
            |i| interpolated_text(original, i),
            interpolated_expression,
            |i| tag_handler(original, i),
        )),
        Vec::new,
        |mut acc: Vec<Element>, item: ParseResult| {
            item.append_to(&mut acc);
            acc
        },
    )(input)
}

fn esi_vars_long<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    // Use parse_vars_content instead of parse_interpolated to avoid infinite recursion
    let (input, _) = tag(b"<esi:vars>")(input)?;
    let (input, elements) = esi_vars_content(original, input)?;
    let (input, _) = tag(b"</esi:vars>")(input)?;

    Ok((input, ParseResult::Multiple(elements)))
}

fn esi_comment(input: &[u8]) -> IResult<&[u8], ParseResult, Error<&[u8]>> {
    map(
        delimited(
            tag(b"<esi:comment"),
            attributes,
            preceded(multispace0, self_closing), // ESI comment must be self-closing per ESI spec
        ),
        |_| ParseResult::Empty,
    )(input)
}

/// Zero-copy esi:remove parser
fn esi_remove<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    let (input, _) = tag(b"<esi:remove>")(input)?;
    let (input, _) = parse_interpolated(original, input)?;
    let (input, _) = tag(b"</esi:remove>")(input)?;
    Ok((input, ParseResult::Empty))
}

fn esi_text<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    map(
        delimited(
            tag(b"<esi:text>"),
            take_until(b"</esi:text>".as_ref()),
            tag(b"</esi:text>"),
        ),
        |v| ParseResult::Single(Element::Text(slice_as_bytes(original, v))),
    )(input)
}
fn esi_include(input: &[u8]) -> IResult<&[u8], ParseResult, Error<&[u8]>> {
    map(
        delimited(
            tag(b"<esi:include"),
            attributes,
            preceded(multispace0, alt((closing_bracket, self_closing))),
        ),
        |mut attrs| {
            let src = attrs.remove("src").map(Bytes::from).unwrap_or_default();
            let alt = attrs.remove("alt").map(Bytes::from);
            let continue_on_error = attrs
                .get("onerror")
                .map(|s| s == "continue")
                .unwrap_or(false);

            ParseResult::Single(Element::Esi(Tag::Include {
                src,
                alt,
                continue_on_error,
            }))
        },
    )(input)
}

fn attributes(input: &[u8]) -> IResult<&[u8], HashMap<String, String>, Error<&[u8]>> {
    // map(
    //     many0(separated_pair(
    //         preceded(multispace1, alpha1),
    //         tag(b"="),
    //         htmlstring,
    //     )),
    //     |pairs| {
    //         pairs
    //             .into_iter()
    //             .map(|(k, v)| (bytes_to_string(k), bytes_to_string(v)))
    //             .collect()
    //     },
    // )(input)
    fold_many0(
        separated_pair(preceded(multispace1, alpha1), tag(b"="), htmlstring),
        HashMap::new,
        |mut acc, (k, v)| {
            acc.insert(bytes_to_string(k), bytes_to_string(v));
            acc
        },
    )(input)
}

fn htmlstring(input: &[u8]) -> IResult<&[u8], &[u8], Error<&[u8]>> {
    alt((
        delimited(
            double_quote,
            take_while(|c| !is_double_quote(c)),
            double_quote,
        ),
        delimited(
            single_quote,
            take_while(|c| !is_single_quote(c)),
            single_quote,
        ),
    ))(input)
}

// Used by parse_interpolated - zero-copy with original Bytes reference
fn interpolated_text<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    map(
        recognize(take_while1(|c| !is_opening_bracket(c) && !is_dollar(c))),
        |s: &[u8]| ParseResult::Single(Element::Text(slice_as_bytes(original, s))),
    )(input)
}

// ============================================================================
// Zero-Copy HTML/Text Parsers
// ============================================================================
/// Helper to find and consume the closing '>' character
#[inline]
fn closing_bracket(input: &[u8]) -> IResult<&[u8], &[u8], Error<&[u8]>> {
    tag(b">")(input)
}

/// Helper to find and consume the closing self-closing tag characters '/>'
#[inline]
fn self_closing(input: &[u8]) -> IResult<&[u8], &[u8], Error<&[u8]>> {
    tag(b"/>")(input)
}

/// Helper to find and consume the opening '<' character
#[inline]
fn opening_bracket(input: &[u8]) -> IResult<&[u8], &[u8], Error<&[u8]>> {
    tag(b"<")(input)
}

/// Helper to find and consume the closing double quote character
#[inline]
fn double_quote(input: &[u8]) -> IResult<&[u8], &[u8], Error<&[u8]>> {
    tag(b"\"")(input)
}

/// Helper to find and consume the closing single quote character
#[inline]
fn single_quote(input: &[u8]) -> IResult<&[u8], &[u8], Error<&[u8]>> {
    tag(b"\'")(input)
}

#[inline]
fn is_closing_bracket(b: u8) -> bool {
    b == b'>'
}

#[inline]
fn is_double_quote(b: u8) -> bool {
    b == b'\"'
}

#[inline]
fn is_single_quote(b: u8) -> bool {
    b == b'\''
}

/// Check if byte can start an HTML/XML tag name (including special constructs like <!--, <!DOCTYPE, <![CDATA[)
#[inline]
fn is_tag_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'!'
}

/// Check if byte can continue an HTML/XML tag name
#[inline]
fn is_tag_cont(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.' | b':' | b'[')
}

/// Parse an HTML/XML-style tag name.
/// Returns the subslice of the original input containing only the tag name.
#[inline]
fn tag_name(input: &[u8]) -> IResult<&[u8], &[u8], Error<&[u8]>> {
    recognize(nom::sequence::pair(
        take_while_m_n(1, 1, is_tag_start), // first letter
        take_while(is_tag_cont),            // rest of name
    ))(input)
}

/// Parse a complete opening tag, returning (tag_name, remaining_after_tag, full_tag_slice)
/// Only succeeds when we have a complete tag (ending with > or />)
fn complete_opening_tag(input: &[u8]) -> IResult<&[u8], (&[u8], &[u8]), Error<&[u8]>> {
    let start = input;

    // Parse <tagname
    let (rest, _) = opening_bracket(input)?;
    let (rest, name) = tag_name(rest)?;

    // Parse attributes - consume everything up to '>'
    let (rest, _) = take_till(is_closing_bracket)(rest)?;

    // Must have > to be complete
    let (rest, _) = closing_bracket(rest)?;

    Ok((rest, (name, start)))
}

// ============================================================================
// Unified Tag Dispatcher
// ============================================================================

/// Single dispatcher for ALL tags - ESI, HTML script, comments, regular HTML
/// Parses tag name once, then dispatches to specific handlers
fn tag_handler<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    alt((
        // Try HTML comment first (special syntax `<!--`)
        |i| html_comment_content(original, i),
        // Try closing tag (starts with `</`)
        |i| closing_tag(original, i),
        // Try opening tags (parses tag name once, then dispatches)
        |i| {
            // First, parse the complete opening tag (including >)
            // This ensures we don't dispatch on partial tag names like "esi:ass"
            let (rest, (name, start)) = complete_opening_tag(i)?;
            // Dispatch based on tag name without re-parsing
            match name {
                // ESI tags - pass start position to parse from <esi:tagname
                b"esi:assign" => esi_assign(original, start),
                b"esi:include" => esi_include(start),
                b"esi:vars" => esi_vars(original, start),
                b"esi:comment" => esi_comment(start),
                b"esi:remove" => esi_remove(original, start),
                b"esi:text" => esi_text(original, start),
                b"esi:choose" => esi_choose(original, start),
                b"esi:try" => esi_try(original, start),
                b"esi:when" => esi_when(original, start),
                b"esi:otherwise" => esi_otherwise(original, start),
                b"esi:attempt" => esi_attempt(original, start),
                b"esi:except" => esi_except(original, start),

                // Special HTML tags - pass start to re-parse from beginning
                // (script needs to check attributes, so easier to re-parse than continue)
                _ if name.eq_ignore_ascii_case(b"script") => html_script_tag(original, start),

                // Regular HTML tag - continue parsing from where we left off
                _ => {
                    let full_tag = &start[..start.len() - rest.len()];
                    Ok((
                        rest,
                        ParseResult::Single(Element::Html(slice_as_bytes(original, full_tag))),
                    ))
                }
            }
        },
    ))(input)
}

/// Parse HTML comment - input starts at <!--
fn html_comment_content<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    map(
        delimited(tag(b"<!--"), take_until(b"-->".as_ref()), tag(b"-->")),
        |s: &[u8]| ParseResult::Single(Element::Html(slice_as_bytes(original, s))),
    )(input)
}

/// Helper to find closing script tag, handling any content including other closing tags
/// Looks for </script (case insensitive) and returns content before it  
fn script_content(input: &[u8]) -> IResult<&[u8], &[u8], Error<&[u8]>> {
    // recognize(many_till(take(1usize), peek(tag_no_case(b"</script"))))(input)
    // Scan for </script (case insensitive) - much faster than many_till
    const CLOSING_SCRIPT: &[u8] = b"</script";

    for i in 0..input.len() {
        if i + CLOSING_SCRIPT.len() <= input.len() {
            let window = &input[i..i + CLOSING_SCRIPT.len()];
            if window.eq_ignore_ascii_case(CLOSING_SCRIPT) {
                return Ok((&input[i..], &input[..i]));
            }
        }
    }

    // Not found - need more data (streaming)
    Err(nom::Err::Incomplete(nom::Needed::Unknown))
}
/// script tag parser - input starts at <script
/// Treats all script tags (inline and external) as HTML elements
fn html_script_tag<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    let start = input;

    // Parse opening tag
    let (input, _) = recognize(delimited(
        tag_no_case(b"<script"),
        take_till(is_closing_bracket),
        closing_bracket,
    ))(input)?;

    // Parse content (if any) and closing tag (if any)
    let (input, _) = opt(tuple((
        script_content,
        recognize(delimited(
            tag_no_case(b"</script"),
            multispace0,
            closing_bracket,
        )),
    )))(input)?;

    // Return entire script tag as single HTML element
    let full_script = &start[..start.len() - input.len()];
    Ok((
        input,
        ParseResult::Single(Element::Html(slice_as_bytes(original, full_script))),
    ))
}

// ============================================================================
// ESI Tag Parsers (continue from where tag_dispatch left off)
// ============================================================================

fn closing_tag<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    // Reject ESI closing tags before trying to parse
    let (_, _) = peek(not(tag(b"</esi:")))(input)?;

    map(
        recognize(tuple((tag(b"</"), tag_name, multispace0, closing_bracket))),
        |s: &[u8]| ParseResult::Single(Element::Html(slice_as_bytes(original, s))),
    )(input)
}

fn text<'a>(original: &Bytes, input: &'a [u8]) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    map(
        recognize(take_while1(|c| !is_opening_bracket(c))),
        |s: &[u8]| ParseResult::Single(Element::Text(slice_as_bytes(original, s))),
    )(input)
}

/// Check if byte is the opening bracket '<'
#[inline]
fn is_opening_bracket(b: u8) -> bool {
    b == b'<'
}

/// Check if byte is a dollar sign '$'
#[inline]
fn is_dollar(b: u8) -> bool {
    b == b'$'
}
#[inline]
fn is_alphanumeric_or_underscore(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

#[inline]
fn is_lower_alphanumeric_or_underscore(c: u8) -> bool {
    c.is_ascii_lowercase() || c.is_ascii_digit() || c == b'_'
}

fn esi_fn_name(input: &[u8]) -> IResult<&[u8], String, Error<&[u8]>> {
    map(
        preceded(
            complete_bytes::tag(b"$"),
            complete_bytes::take_while1(is_lower_alphanumeric_or_underscore),
        ),
        bytes_to_string,
    )(input)
}

fn esi_var_name(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    map(
        tuple((
            complete_bytes::take_while1(is_alphanumeric_or_underscore),
            opt(delimited(
                complete_bytes::tag(b"{"),
                esi_var_key_expr,
                complete_bytes::tag(b"}"),
            )),
            opt(preceded(complete_bytes::tag(b"|"), fn_nested_argument)),
        )),
        |(name, key, default): (&[u8], _, _)| {
            Expr::Variable(
                bytes_to_string(name),
                key.map(Box::new),
                default.map(Box::new),
            )
        },
    )(input)
}

fn not_dollar_or_curlies(input: &[u8]) -> IResult<&[u8], String, Error<&[u8]>> {
    map(
        complete_bytes::take_while(|c| c != b'$' && c != b'{' && c != b'}' && c != b',' && c != b'"'),
        bytes_to_string,
    )(input)
}

// TODO: handle escaping
fn single_quoted_string(input: &[u8]) -> IResult<&[u8], String, Error<&[u8]>> {
    map(
        delimited(
            complete_bytes::tag(b"'"),
            complete_bytes::take_while(|c| !is_single_quote(c)),
            complete_bytes::tag(b"'"),
        ),
        bytes_to_string,
    )(input)
}
fn triple_quoted_string(input: &[u8]) -> IResult<&[u8], String, Error<&[u8]>> {
    map(
        delimited(
            complete_bytes::tag(b"'''"),
            complete_bytes::take_until("'''"),
            complete_bytes::tag(b"'''"),
        ),
        bytes_to_string,
    )(input)
}

fn string(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    map(
        alt((single_quoted_string, triple_quoted_string)),
        |string: String| {
            if string.is_empty() {
                Expr::String(None)
            } else {
                Expr::String(Some(string))
            }
        },
    )(input)
}

fn var_key(input: &[u8]) -> IResult<&[u8], String, Error<&[u8]>> {
    alt((
        single_quoted_string,
        triple_quoted_string,
        not_dollar_or_curlies,
    ))(input)
}

/// Parse subscript key - can be a string or a nested variable expression
fn esi_var_key_expr(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    alt((
        // Try to parse as a variable first (e.g., $(keyVar))
        esi_variable,
        // Otherwise parse as a string
        map(var_key, |s: String| Expr::String(Some(s))),
    ))(input)
}

fn fn_argument(input: &[u8]) -> IResult<&[u8], Vec<Expr>, Error<&[u8]>> {
    let (input, mut parsed) = separated_list0(
        tuple((
            complete_char::multispace0,
            complete_bytes::tag(b","),
            complete_char::multispace0,
        )),
        fn_nested_argument,
    )(input)?;

    // If the parsed list contains a single empty string element return an empty vec
    if parsed.len() == 1 && parsed[0] == Expr::String(None) {
        parsed = vec![];
    }
    Ok((input, parsed))
}

fn fn_nested_argument(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    alt((esi_function, esi_variable, string, integer, bareword))(input)
}

fn integer(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    map_res(
        recognize(tuple((
            opt(complete_bytes::tag(b"-")),
            complete_bytes::take_while1(|c: u8| c.is_ascii_digit()),
        ))),
        |s: &[u8]| String::from_utf8_lossy(s).parse::<i32>().map(Expr::Integer),
    )(input)
}

fn bareword(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    map(
        complete_bytes::take_while1(is_alphanumeric_or_underscore),
        |name: &[u8]| Expr::Variable(bytes_to_string(name), None, None),
    )(input)
}

fn esi_function(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    let (input, parsed) = tuple((
        esi_fn_name,
        delimited(
            terminated(complete_bytes::tag(b"("), complete_char::multispace0),
            fn_argument,
            preceded(complete_char::multispace0, complete_bytes::tag(b")")),
        ),
    ))(input)?;

    let (name, args) = parsed;

    Ok((input, Expr::Call(name, args)))
}

fn esi_variable(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    delimited(
        complete_bytes::tag(b"$("),
        esi_var_name,
        complete_bytes::tag(b")"),
    )(input)
}

fn operator(input: &[u8]) -> IResult<&[u8], Operator, Error<&[u8]>> {
    alt((
        // Try longer operators first
        map(complete_bytes::tag(b"matches_i"), |_| {
            Operator::MatchesInsensitive
        }),
        map(complete_bytes::tag(b"matches"), |_| Operator::Matches),
        map(complete_bytes::tag(b"=="), |_| Operator::Equals),
        map(complete_bytes::tag(b"!="), |_| Operator::NotEquals),
        map(complete_bytes::tag(b"<="), |_| Operator::LessThanOrEqual),
        map(complete_bytes::tag(b">="), |_| Operator::GreaterThanOrEqual),
        map(complete_bytes::tag(b"<"), |_| Operator::LessThan),
        map(complete_bytes::tag(b">"), |_| Operator::GreaterThan),
        map(complete_bytes::tag(b"&&"), |_| Operator::And),
        map(complete_bytes::tag(b"||"), |_| Operator::Or),
    ))(input)
}

fn interpolated_expression(input: &[u8]) -> IResult<&[u8], ParseResult, Error<&[u8]>> {
    map(alt((esi_function, esi_variable)), |expr| {
        ParseResult::Single(Element::Expr(expr))
    })(input)
}

fn primary_expr(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    alt((
        // Parse negation: !expr
        map(
            preceded(
                complete_bytes::tag(b"!"),
                preceded(complete_char::multispace0, primary_expr),
            ),
            |expr| Expr::Not(Box::new(expr)),
        ),
        // Parse grouped expression: (expr)
        delimited(
            complete_bytes::tag(b"("),
            delimited(complete_char::multispace0, expr, complete_char::multispace0),
            complete_bytes::tag(b")"),
        ),
        // Parse basic expressions
        esi_function,
        esi_variable,
        integer,
        string,
    ))(input)
}

fn expr(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    let (rest, exp) = primary_expr(input)?;

    if let Ok((rest, (operator, right_exp))) = tuple((
        delimited(
            complete_char::multispace0,
            operator,
            complete_char::multispace0,
        ),
        expr,
    ))(rest)
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
fn expression(input: &[u8]) -> IResult<&[u8], Vec<Element>, Error<&[u8]>> {
    map(expr, |x| vec![Element::Expr(x)])(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_choose() {
        let input = b"<esi:choose></esi:choose>";
        let bytes = Bytes::from_static(input);
        let result = parse_complete(&bytes);
        match result {
            Ok((rest, _)) => {
                assert_eq!(rest.len(), 0, "Should parse completely");
            }
            Err(e) => {
                panic!("Parse failed with error: {:?}", e);
            }
        }
    }

    #[test]
    fn test_choose_with_when() {
        let input = b"<esi:choose><esi:when test=\"1\">hi</esi:when></esi:choose>";
        let bytes = Bytes::from_static(input);
        let result = parse_complete(&bytes);
        match result {
            Ok((rest, result)) => {
                if rest.is_empty() {
                    println!("Success! Result: {:?}", result);
                } else {
                    panic!(
                        "Did not parse completely. Remaining: {:?}",
                        String::from_utf8_lossy(rest)
                    );
                }
            }
            Err(e) => {
                panic!("Parse failed with error: {:?}", e);
            }
        }
    }

    #[test]
    fn test_parse() {
        let input = br#"
<a>foo</a>
<bar />
baz
<esi:vars name="$(hello)"/>
<esi:vars>
hello <br>
</esi:vars>
<sCripT src="whatever">
<baz>
<script> less </fuckery more </script>
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
        let bytes = Bytes::from_static(input);
        let result = parse_complete(&bytes);
        match result {
            Ok((rest, _)) => {
                // Just test to make sure it parsed the whole thing
                if !rest.is_empty() {
                    panic!(
                        "Failed to parse completely. Remaining: {:?}",
                        String::from_utf8_lossy(rest)
                    );
                }
            }
            Err(e) => {
                panic!("Parse failed with error: {:?}", e);
            }
        }
    }
    #[test]
    fn test_parse_script() {
        let input = b"<sCripT> less < more </scRIpt>";
        let bytes = Bytes::from_static(input);
        let (rest, x) = html_script_tag(&bytes, input).unwrap();
        assert_eq!(rest.len(), 0);
        assert!(matches!(
            x,
            ParseResult::Single(Element::Html(ref h)) if h.as_ref() == b"<sCripT> less < more </scRIpt>"
        ));
    }
    #[test]
    fn test_parse_script_with_src() {
        let input = b"<sCripT src=\"whatever\"></sCripT>";
        let bytes = Bytes::from_static(input);
        let (rest, x) = html_script_tag(&bytes, input).unwrap();
        assert_eq!(rest.len(), 0);
        assert!(matches!(
            x,
            ParseResult::Single(Element::Html(ref h)) if h.as_ref() == b"<sCripT src=\"whatever\"></sCripT>"
        ));
    }
    #[test]
    fn test_parse_esi_vars_short() {
        let input = br#"<esi:vars name="$(hello)"/>"#;
        let bytes = Bytes::from_static(input);
        let (rest, x) = esi_vars(&bytes, input).unwrap();
        assert_eq!(rest.len(), 0);
        // esi_vars returns Multiple when parsing short form with expression
        if let ParseResult::Multiple(elements) = x {
            assert_eq!(elements.len(), 1);
            assert!(matches!(
                &elements[0],
                Element::Expr(Expr::Variable(name, None, None)) if name == "hello"
            ));
        } else {
            panic!("Expected ParseResult::Multiple");
        }
    }
    #[test]
    fn test_parse_esi_vars_long() {
        // Nested <esi:vars> tags are not supported to prevent infinite recursion
        // The inner <esi:vars> tags should be treated as plain text/HTML
        let input = br#"<esi:vars>hello<br></esi:vars>"#;
        let bytes = Bytes::from_static(input);
        let (rest, x) = parse_complete(&bytes).unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(
            x,
            [
                Element::Text(Bytes::from_static(b"hello")),
                Element::Html(Bytes::from_static(b"<br>")),
            ]
        );
    }

    #[test]
    fn test_nested_vars() {
        // Nested <esi:vars> tags ARE supported - the inner vars tag is parsed recursively
        let input = br#"<esi:vars>outer<esi:vars>inner</esi:vars></esi:vars>"#;
        let bytes = Bytes::from_static(input);
        let (rest, elements) = parse_complete(&bytes).unwrap();

        assert_eq!(rest.len(), 0, "Should parse completely");
        assert_eq!(
            elements,
            [
                Element::Text(Bytes::from_static(b"outer")),
                Element::Text(Bytes::from_static(b"inner")),
            ]
        );
    }
    #[test]
    fn test_parse_complex_expr() {
        let input = br#"<esi:vars name="$call('hello') matches $(var{'key'})"/>"#;
        let bytes = Bytes::from_static(input);
        let (rest, x) = parse_complete(&bytes).unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(
            x,
            [Element::Expr(Expr::Comparison {
                left: Box::new(Expr::Call(
                    "call".to_string(),
                    vec![Expr::String(Some("hello".to_string()))]
                )),
                operator: Operator::Matches,
                right: Box::new(Expr::Variable(
                    "var".to_string(),
                    Some(Box::new(Expr::String(Some("key".to_string())))),
                    None
                ))
            })]
        );
    }

    #[test]
    fn test_vars_with_content() {
        let input = br#"<esi:vars>
            $(QUERY_STRING{param})
        </esi:vars>"#;
        let bytes = Bytes::from_static(input);
        let result = esi_vars_long(&bytes, input);
        assert!(
            result.is_ok(),
            "esi_vars_long should parse successfully: {:?}",
            result.err()
        );
        let (rest, _elements) = result.unwrap();
        assert_eq!(
            rest.len(),
            0,
            "Parser should consume all input. Remaining: '{:?}'",
            String::from_utf8_lossy(rest)
        );
    }

    #[test]
    fn test_exact_failing_input() {
        // This is the exact input from the failing test
        let input = br#"
        <esi:assign name="keyVar" value="'param'" />
        <esi:vars>
            $(QUERY_STRING{param})
            $(QUERY_STRING{$(keyVar)})
        </esi:vars>
    "#;
        let bytes = Bytes::from_static(input);
        let (rest, elements) = parse_complete(&bytes).unwrap();
        eprintln!("Chunks: {:?}", elements);
        eprintln!("Remaining: {:?}", String::from_utf8_lossy(rest));
        assert_eq!(
            rest.len(),
            0,
            "Parser should consume all input. Remaining: '{:?}'",
            String::from_utf8_lossy(rest)
        );
    }

    #[test]
    fn test_esi_vars_directly() {
        let input = br#"<esi:vars>
            $(QUERY_STRING{param})
            $(QUERY_STRING{$(keyVar)})
        </esi:vars>"#;
        let bytes = Bytes::from_static(input);
        let result = esi_vars(&bytes, input);
        assert!(result.is_ok(), "esi_vars should parse: {:?}", result.err());
        let (rest, _) = result.unwrap();
        assert_eq!(rest.len(), 0, "Should consume all input");
    }

    #[test]
    fn test_esi_tag_on_vars() {
        let input = br#"<esi:vars>
            $(QUERY_STRING{param})
        </esi:vars>"#;
        let bytes = Bytes::from_static(input);
        let (rest, _result) = esi_vars(&bytes, input).unwrap();
        assert_eq!(rest.len(), 0, "Parser should consume all input");
    }

    #[test]
    fn test_assign_then_vars() {
        // Test simple case without nested variables (which aren't supported yet)
        let input =
            br#"<esi:assign name="key" value="'val'" /><esi:vars>$(QUERY_STRING{param})</esi:vars>"#;
        let bytes = Bytes::from_static(input);
        let (rest, _elements) = parse_complete(&bytes).unwrap();
        assert_eq!(rest.len(), 0);
    }

    #[test]
    fn test_parse_plain_text() {
        let input = b"hello\nthere";
        let bytes = Bytes::from_static(input);
        let (rest, x) = parse_complete(&bytes).unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(x, [Element::Text(Bytes::from_static(b"hello\nthere"))]);
    }
    #[test]
    fn test_parse_interpolated() {
        let input = b"hello $(foo)<esi:vars>goodbye $(foo)</esi:vars>";
        let bytes = Bytes::from_static(input);
        let (rest, x) = parse_complete(&bytes).unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(
            x,
            [
                Element::Text(Bytes::from_static(b"hello $(foo)")),
                Element::Text(Bytes::from_static(b"goodbye ")),
                Element::Expr(Expr::Variable("foo".to_string(), None, None)),
            ]
        );
    }
    #[test]
    fn test_parse_examples() {
        let input = include_bytes!("../../examples/esi_vars_example/src/index.html");
        let bytes = Bytes::from_static(input);
        let (rest, _) = parse_complete(&bytes).unwrap();
        // just make sure it parsed the whole thing
        assert_eq!(rest.len(), 0);
    }

    #[test]
    fn test_parse_equality_operators() {
        let input = b"$(foo) == 'bar'";
        let (rest, result) = expr(input).unwrap();
        assert_eq!(rest.len(), 0);
        assert!(matches!(
            result,
            Expr::Comparison {
                operator: Operator::Equals,
                ..
            }
        ));

        let input2 = b"$(foo) != 'bar'";
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
        // Test via parsing complete ESI documents with esi:when test attributes
        // which internally use parse_expression() for complete input handling

        let input1 = b"<esi:choose><esi:when test=\"$(count) < 10\">yes</esi:when></esi:choose>";
        let bytes1 = Bytes::from_static(input1);
        let result1 = parse_complete(&bytes1);
        assert!(
            result1.is_ok(),
            "Should parse < operator: {:?}",
            result1.err()
        );

        let input2 = b"<esi:choose><esi:when test=\"$(count) >= 5\">yes</esi:when></esi:choose>";
        let bytes2 = Bytes::from_static(input2);
        let result2 = parse_complete(&bytes2);
        assert!(
            result2.is_ok(),
            "Should parse >= operator: {:?}",
            result2.err()
        );
    }

    #[test]
    fn test_parse_logical_operators() {
        // With parentheses to enforce correct precedence
        let input = b"($(foo) == 'bar') && ($(baz) == 'qux')";
        let (rest, result) = expr(input).unwrap();
        assert_eq!(rest.len(), 0);
        assert!(matches!(
            result,
            Expr::Comparison {
                operator: Operator::And,
                ..
            }
        ));

        let input2 = b"($(foo) == 'bar') || ($(baz) == 'qux')";
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
        let input = b"!$(flag)";
        let (rest, result) = expr(input).unwrap();
        assert_eq!(rest.len(), 0);
        assert!(matches!(result, Expr::Not(_)));

        // Test negation with comparison
        let input2 = b"!($(foo) == 'bar')";
        let (rest, result) = expr(input2).unwrap();
        assert_eq!(rest.len(), 0);
        assert!(matches!(result, Expr::Not(_)));
    }

    #[test]
    fn test_parse_grouped_expressions() {
        let input = b"($(foo) == 'bar')";
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
    fn test_single_quoted_attributes() {
        // Test single-quoted attributes
        let input = b"<esi:include src='http://example.com/fragment' />";
        let bytes = Bytes::from_static(input);
        let (rest, elements) = parse_complete(&bytes).unwrap();
        assert_eq!(rest.len(), 0, "Should parse completely");
        assert_eq!(elements.len(), 1);
        if let Element::Esi(Tag::Include { src, .. }) = &elements[0] {
            assert_eq!(src.as_ref(), b"http://example.com/fragment");
        } else {
            panic!("Expected Include tag");
        }

        // Test mixed quotes
        let input2 = b"<esi:assign name='foo' value=\"bar\" />";
        let bytes2 = Bytes::from_static(input2);
        let (rest, elements) = parse_complete(&bytes2).unwrap();
        assert_eq!(rest.len(), 0, "Should parse completely");
        assert_eq!(elements.len(), 1);
        if let Element::Esi(Tag::Assign { name, value }) = &elements[0] {
            assert_eq!(name, "foo");
            assert_eq!(value, &Expr::String(Some("bar".to_string())));
        } else {
            panic!("Expected Assign tag");
        }
    }
    #[test]
    fn test_unclosed_script_tag() {
        // Unclosed script tag - should handle gracefully
        let input = b"<script>content without closing";
        let bytes = Bytes::from_static(input);
        let (rest, elements) = parse_complete(&bytes).unwrap();

        // In complete mode, unclosed script becomes text
        assert_eq!(rest.len(), 0, "Should consume all input");
        assert_eq!(elements.len(), 1);
        // The whole thing becomes text since script tag couldn't be fully parsed
        assert!(matches!(&elements[0], Element::Text(_)));
    }
    #[test]
    fn test_partial_esi_tag() {
        // Partial ESI tag - streaming should return Incomplete
        let input = b"<esi:inclu";
        let bytes = Bytes::from_static(input);
        let result = parse(&bytes);

        // Should return Incomplete in streaming mode
        assert!(matches!(result, Err(nom::Err::Incomplete(_))));
    }

    #[test]
    fn test_partial_esi_tag_with_prefix() {
        // Text followed by partial ESI tag
        let input = b"hello <esi:inclu";
        let bytes = Bytes::from_static(input);
        let result = parse(&bytes);

        // Should return the text and indicate more data needed
        match result {
            Ok((rest, elements)) => {
                // Should have parsed "hello " as text
                assert_eq!(elements.len(), 1);
                assert!(matches!(&elements[0], Element::Text(t) if t.as_ref() == b"hello "));
                // Remaining should be the partial tag
                assert_eq!(rest, b"<esi:inclu");
            }
            Err(nom::Err::Incomplete(_)) => {
                // This is also acceptable - couldn't parse anything
            }
            Err(e) => panic!("Unexpected error: {:?}", e),
        }
    }
}
