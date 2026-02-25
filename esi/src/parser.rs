use bytes::Bytes;
// Using STREAMING parsers for document structure - they return Incomplete when they need more data
// This enables TRUE bounded-memory streaming for the main document parsing
use nom::bytes::streaming as streaming_bytes;
use nom::character::streaming as streaming_char;
// Using COMPLETE parsers for expression parsing - expressions are always complete
// (they come from attribute values which are fully extracted before parsing)
use nom::bytes::complete::{tag, take_until, take_while, take_while1};
use nom::character::complete::multispace0;

use nom::branch::alt;
use nom::combinator::{map, map_res, not, opt, peek, recognize};
use nom::error::Error;
use nom::multi::{fold_many0, many0, separated_list0};
use nom::sequence::{delimited, preceded, separated_pair, terminated, tuple};
use nom::IResult;
use std::collections::HashMap;

use crate::parser_types::{Element, Expr, IncludeAttributes, Operator, Tag, WhenBranch};

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
            Self::Single(e) => acc.push(e),
            Self::Multiple(mut v) => acc.append(&mut v),
            Self::Empty => {}
        }
    }
}

/// Zero-copy parse loop that threads Bytes through the parser chain
fn parse_loop<'a, F>(
    original: &'a Bytes,
    mut parser: F,
    incomplete_strategy: &ParsingMode,
) -> IResult<&'a [u8], Vec<Element>, Error<&'a [u8]>>
where
    F: FnMut(&Bytes, &'a [u8]) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>>,
{
    let mut result = Vec::new();
    let mut remaining = original.as_ref();

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
                        // Treat remaining bytes as text - refcount increment, zero-copy
                        if !remaining.is_empty() {
                            result.push(Element::Text(slice_as_bytes(original, remaining)));
                        }
                        Ok((&remaining[remaining.len()..], result))
                    }
                };
            }
            Err(e) => {
                if result.is_empty() {
                    // Return a real parse error
                    return Err(e);
                }
                // Else - return what we have so far
                return Ok((remaining, result));
            }
        }
    }
}

// ============================================================================
// Public APIs - Zero-Copy Streaming Parsers
// ============================================================================

/// Parse input bytes into ESI elements using streaming parsers
///
/// Uses streaming parsers that return `Incomplete` when they need more data.
/// The caller (typically lib.rs) must handle `Incomplete` by reading more data into the buffer.
///
/// # Returns
/// - `Ok((remaining, elements))` - Successfully parsed elements with zero-copy `Bytes` slices
/// - `Err(Incomplete)` - Parser needs more data to continue
/// - `Err(Error)` - Parse error occurred
pub fn parse(input: &Bytes) -> IResult<&[u8], Vec<Element>, Error<&[u8]>> {
    parse_loop(input, element, &ParsingMode::Streaming)
}

/// Parse remaining input when no more data will arrive (at EOF)
///
/// Uses the same streaming parsers as [`parse`], but when they return `Incomplete`,
/// treats the remaining unparseable bytes as literal text instead of requesting more data.
/// Use this when you've reached EOF and want to finalize parsing.
///
/// # Returns
/// - `Ok((remaining, elements))` - Successfully parsed elements, with any unparseable remainder
///   converted to `Text` elements
/// - `Err(Error)` - Parse error occurred (but not `Incomplete`)
pub fn parse_remainder(input: &Bytes) -> IResult<&[u8], Vec<Element>, Error<&[u8]>> {
    parse_loop(input, element, &ParsingMode::Complete)
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Convert bytes to String using lossy UTF-8 conversion
#[inline]
fn bytes_to_string(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// Helper to extract an attribute value from a `HashMap`, removing it
#[inline]
fn take_attr(attrs: &mut HashMap<String, String>, key: &str) -> String {
    attrs.remove(key).unwrap_or_default()
}

/// Helper to extract an optional attribute value from a `HashMap`, removing it
#[inline]
fn take_attr_opt(attrs: &mut HashMap<String, String>, key: &str) -> Option<String> {
    attrs.remove(key)
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

// Used by parse_interpolated - zero-copy with original Bytes reference
fn interpolated_text<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    map(
        recognize(streaming_bytes::take_while1(|c| {
            !is_open_bracket(c) && !is_dollar(c)
        })),
        |s: &[u8]| ParseResult::Single(Element::Text(slice_as_bytes(original, s))),
    )(input)
}

// Complete version for attribute value parsing - doesn't return Incomplete
fn interpolated_text_complete<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    map(
        recognize(take_while1(|c| !is_open_bracket(c) && !is_dollar(c))),
        |s: &[u8]| ParseResult::Single(Element::Text(slice_as_bytes(original, s))),
    )(input)
}

/// Parses a string that may contain interpolated expressions like $(VAR)
/// Accepts &Bytes and returns Bytes slices that reference the original (zero-copy)
///
/// # Errors
/// Returns an error if the string contains invalid ESI expressions (e.g., unclosed $(, invalid variable names)
pub fn interpolated_content(input: &Bytes) -> IResult<&[u8], Vec<Element>, Error<&[u8]>> {
    // NOTE: This function parses complete strings (like attribute values), not streaming input
    // Uses fold_many0 with COMPLETE parsers to avoid Incomplete errors at string boundaries
    fold_many0(
        |i| {
            alt((interpolated_expression, |ii| {
                interpolated_text_complete(input, ii)
            }))(i)
        },
        Vec::new,
        |mut acc: Vec<Element>, item: ParseResult| {
            item.append_to(&mut acc);
            acc
        },
    )(input.as_ref())
}

/// Zero-copy element parser - dispatches to text or tags
/// Note: Variable expressions like $(VAR) in plain HTML are NOT evaluated - only inside ESI tags
fn element<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    // For top-level HTML content, we only parse tags, not variable expressions
    // Variable expressions are only evaluated inside ESI tags
    alt((
        |i| top_level_text(original, i),
        |i| tag_handler(original, i),
    ))(input)
}

/// Text parser for top-level content - stops only at '<', not at '$()'
/// This ensures $(VAR) in plain HTML is treated as literal text
fn top_level_text<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    map(
        recognize(streaming_bytes::take_while1(|c| !is_open_bracket(c))),
        |s: &[u8]| ParseResult::Single(Element::Text(slice_as_bytes(original, s))),
    )(input)
}

fn interpolated_element<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    alt((
        |i| interpolated_text(original, i),
        interpolated_expression,
        |i| tag_handler(original, i),
    ))(input)
}

// Parse a sequence of interpolated elements (text + expressions + tags)
// Used for parsing content inside tags that allow nested ESI
fn tag_content<'a>(
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

/// Validates a variable name according to ESI spec:
/// - Up to 256 alphanumeric characters (A-Z, a-z, 0-9)
/// - Can include underscores (_)
/// - Cannot start with $ (dollar sign) or digit
/// - First character must be alphabetic (A-Z, a-z)
/// - Can include subscript notation with braces {} containing expressions
fn is_valid_variable_name(name: &str) -> bool {
    if name.is_empty() || name.len() > 256 {
        return false;
    }

    // Check if there's a subscript by finding opening brace
    if let Some(brace_pos) = name.find('{') {
        // Has subscript - validate base name and check brace matching
        let base_name = &name[..brace_pos];

        // Validate base name strictly (alphanumeric + underscore, starting with alpha)
        if !is_valid_base_variable_name(base_name) {
            return false;
        }

        // Check that subscript has matching closing brace
        if !name.ends_with('}') {
            return false;
        }

        // Subscript content (between braces) can contain any characters for expressions
        // We don't validate it here - expression parser will handle it
        true
    } else {
        // No subscript - validate as a simple variable name
        is_valid_base_variable_name(name)
    }
}

/// Validates a base variable name (without subscripts):
/// - Must start with alphabetic character
/// - Can only contain alphanumeric characters and underscores
fn is_valid_base_variable_name(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }

    let mut chars = name.chars();

    // First character must be alphabetic
    if let Some(first) = chars.next() {
        if !first.is_ascii_alphabetic() {
            return false;
        }
    } else {
        return false;
    }

    // Remaining characters must be alphanumeric or underscore
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

// Parse variable name with optional subscript like "colors{0}" or "ages{joan}"
fn parse_variable_name_with_subscript(name: &str) -> (String, Option<Expr>) {
    if let Some(brace_pos) = name.find('{') {
        if name.ends_with('}') {
            let var_name = &name[..brace_pos];
            let subscript_str = &name[brace_pos + 1..name.len() - 1];

            // Try to parse the subscript as an expression
            // Check different patterns:
            let subscript_expr = subscript_str.parse::<i32>().map_or_else(
                |_| {
                    if subscript_str
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || c == '_')
                    {
                        // Bare identifier like "joan" - treat as string literal key
                        Some(Expr::String(Some(subscript_str.to_string())))
                    } else if let Ok((_, expr)) = parse_expression(subscript_str) {
                        // Successfully parsed as expression (e.g., "'key'", "$(var)", complex expression)
                        Some(expr)
                    } else {
                        // Failed to parse - ignore subscript
                        None
                    }
                },
                |num| Some(Expr::Integer(num)),
            );

            if let Some(expr) = subscript_expr {
                return (var_name.to_string(), Some(expr));
            }
        }
    }
    (name.to_string(), None)
}

fn esi_assign<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    alt((esi_assign_short, |i| esi_assign_long(original, i)))(input)
}

fn assign_attributes_short(attrs: HashMap<String, String>) -> ParseResult {
    let name = attrs.get("name").cloned().unwrap_or_default();

    // Validate variable name according to ESI spec
    if !is_valid_variable_name(&name) {
        // Invalid name - silently drop this tag per ESI spec for invalid constructs
        // ParseResult::Empty causes the parser to consume the tag but emit nothing
        return ParseResult::Empty;
    }

    // Parse name and optional subscript (e.g., "colors{0}" or "ages{joan}")
    let (var_name, subscript) = parse_variable_name_with_subscript(&name);

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

    ParseResult::Single(Element::Esi(Tag::Assign {
        name: var_name,
        subscript,
        value,
    }))
}

/// Parse an attribute value as an ESI expression
/// Used for parsing src/alt/param values which can contain variables, functions, etc.
/// Examples:
///   "simple_string" -> Expr::String(Some("simple_string"))
///   "$(VARIABLE)" -> Expr::Variable("VARIABLE", ...)
///   "http://example.com/?q=$(QUERY_STRING{'query'})" -> Expr::Interpolated([Text, Expr])
fn parse_attr_as_expr(value_str: String) -> Expr {
    parse_attr_as_expr_with_context(value_str, false)
}

fn parse_attr_as_expr_with_context(value_str: String, bare_id_as_variable: bool) -> Expr {
    // Fast-path: empty string
    if value_str.is_empty() {
        return Expr::String(Some(String::new()));
    }

    // Try to parse as pure ESI expression first (variables/functions/quoted strings/integers/dict/list literals)
    if let Ok((remaining, expr)) = parse_expression(&value_str) {
        // Only accept if we consumed the entire string (pure expression)
        if remaining.is_empty() {
            return expr;
        }
    }

    // Special case: bare identifier (e.g., "items" for collection="items")
    // Whether to treat as variable depends on context
    if bare_id_as_variable {
        let is_bare_identifier = value_str
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_')
            && value_str
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic() || c == '_');

        if is_bare_identifier {
            return Expr::Variable(value_str, None, None);
        }
    }

    // Not a pure expression - try interpolation (mixed text + expressions)
    let bytes = Bytes::from(value_str);
    match interpolated_content(&bytes) {
        Ok(([], elements)) => {
            if elements.len() == 1 {
                match elements.into_iter().next().unwrap() {
                    Element::Expr(expr) => expr,
                    Element::Text(text) => {
                        Expr::String(Some(String::from_utf8_lossy(&text).into_owned()))
                    }
                    _ => Expr::String(Some(String::from_utf8_lossy(&bytes).into_owned())),
                }
            } else if !elements.is_empty() {
                Expr::Interpolated(elements)
            } else {
                Expr::String(Some(String::new()))
            }
        }
        _ => Expr::String(Some(String::from_utf8_lossy(&bytes).into_owned())),
    }
}

fn assign_long(attrs: &HashMap<String, String>, mut content: Vec<Element>) -> ParseResult {
    let name = attrs.get("name").cloned().unwrap_or_default();

    // Validate variable name according to ESI spec
    if !is_valid_variable_name(&name) {
        // Invalid name - silently drop this tag per ESI spec for invalid constructs
        // ParseResult::Empty causes the parser to consume the tag but emit nothing
        return ParseResult::Empty;
    }

    // Parse name and optional subscript (e.g., "colors{0}" or "ages{joan}")
    let (var_name, subscript) = parse_variable_name_with_subscript(&name);

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

    ParseResult::Single(Element::Esi(Tag::Assign {
        name: var_name,
        subscript,
        value,
    }))
}

fn esi_assign_short(input: &[u8]) -> IResult<&[u8], ParseResult, Error<&[u8]>> {
    map(
        delimited(
            streaming_bytes::tag(b"<esi:assign"),
            attributes,
            preceded(streaming_char::multispace0, streaming_self_closing),
        ),
        assign_attributes_short,
    )(input)
}

fn esi_assign_long<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    // Per ESI spec, esi:assign cannot contain nested ESI tags - only text and expressions
    // Capture content first with take_until, then parse as complete
    map(
        tuple((
            delimited(
                streaming_bytes::tag(b"<esi:assign"),
                attributes,
                preceded(streaming_char::multispace0, streaming_close_bracket),
            ),
            streaming_bytes::take_until(b"</esi:assign>".as_ref()),
            streaming_bytes::tag(b"</esi:assign>"),
        )),
        |(attrs, content, _)| {
            // Parse the captured content in complete mode (text + expressions only)
            let elements = parse_content_complete(original, content);
            assign_long(&attrs, elements)
        },
    )(input)
}

// ============================================================================
// Generic Container Tag Parser
// ============================================================================

/// Generic parser for container tags (tags with opening/closing pairs and content)
/// This reduces duplication for tags like <esi:attempt>, <esi:except>, <esi:otherwise>
fn parse_container_tag<'a>(
    original: &Bytes,
    input: &'a [u8],
    opening_tag: &'static [u8],
    closing_tag: &'static [u8],
    constructor: impl FnOnce(Vec<Element>) -> Tag,
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    let (input, content) = delimited(
        streaming_bytes::tag(opening_tag),
        |i| tag_content(original, i),
        streaming_bytes::tag(closing_tag),
    )(input)?;

    Ok((
        input,
        ParseResult::Single(Element::Esi(constructor(content))),
    ))
}

fn esi_except<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    parse_container_tag(
        original,
        input,
        b"<esi:except>",
        b"</esi:except>",
        Tag::Except,
    )
}

fn esi_attempt<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    parse_container_tag(
        original,
        input,
        b"<esi:attempt>",
        b"</esi:attempt>",
        Tag::Attempt,
    )
}

// Zero-copy version used by both esi_tag and esi_tag_old (via parse_interpolated)
fn esi_try<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    let (input, _) = streaming_bytes::tag(b"<esi:try>")(input)?;
    let (input, v) = tag_content(original, input)?;
    let (input, _) = streaming_bytes::tag(b"</esi:try>")(input)?;

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
            streaming_bytes::tag(b"<esi:otherwise>"),
            |i| tag_content(original, i),
            streaming_bytes::tag(b"</esi:otherwise>"),
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
                streaming_bytes::tag(b"<esi:when"),
                attributes,
                preceded(
                    streaming_char::multispace0,
                    alt((streaming_close_bracket, streaming_self_closing)),
                ),
            ),
            |i| tag_content(original, i),
            streaming_bytes::tag(b"</esi:when>"),
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

/// Parse <esi:foreach collection="..." item="...">...</esi:foreach>
fn esi_foreach<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    map(
        tuple((
            delimited(
                streaming_bytes::tag(b"<esi:foreach"),
                attributes,
                preceded(streaming_char::multispace0, streaming_close_bracket),
            ),
            |i| tag_content(original, i),
            streaming_bytes::tag(b"</esi:foreach>"),
        )),
        |(attrs, content, _)| {
            let collection_str = attrs.get("collection").cloned().unwrap_or_default();
            let collection = parse_attr_as_expr_with_context(collection_str, true);
            let item = attrs.get("item").cloned();

            ParseResult::Single(Element::Esi(Tag::Foreach {
                collection,
                item,
                content,
            }))
        },
    )(input)
}

/// Parse <esi:break />
fn esi_break(input: &[u8]) -> IResult<&[u8], ParseResult, Error<&[u8]>> {
    map(
        delimited(
            streaming_bytes::tag(b"<esi:break"),
            streaming_char::multispace0,
            streaming_self_closing,
        ),
        |_| ParseResult::Single(Element::Esi(Tag::Break)),
    )(input)
}

/// Zero-copy parser for <esi:choose>...</esi:choose>
fn esi_choose<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    let (input, _) = streaming_bytes::tag(b"<esi:choose>")(input)?;
    let (input, v) = tag_content(original, input)?;
    let (input, _) = streaming_bytes::tag(b"</esi:choose>")(input)?;

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

fn parse_vars_attributes(mut attrs: HashMap<String, String>) -> Result<ParseResult, &'static str> {
    take_attr_opt(&mut attrs, "name").map_or_else(
        || Err("no name field in short form vars"),
        |name_val| {
            if let Ok((_, expr)) = parse_expression(&name_val) {
                Ok(ParseResult::Single(Element::Expr(expr)))
            } else {
                Err("failed to parse expression")
            }
        },
    )
}

fn esi_vars_short(input: &[u8]) -> IResult<&[u8], ParseResult, Error<&[u8]>> {
    map_res(
        delimited(
            streaming_bytes::tag(b"<esi:vars"),
            attributes,
            preceded(streaming_char::multispace0, streaming_self_closing), // Short form must be self-closing per ESI spec
        ),
        parse_vars_attributes,
    )(input)
}

/// Parse content for tags that don't support nested ESI (text + expressions + HTML only)
/// Uses COMPLETE mode - input must be captured entirely before calling this
/// Parses: text, expressions ($...), and HTML tags
/// Does NOT parse: nested ESI tags (treated as literal text)
fn parse_content_complete(original: &Bytes, content: &[u8]) -> Vec<Element> {
    // Text in complete mode - stops at $ or < for expression/tag parsing
    fn text_complete<'a>(
        original: &Bytes,
        input: &'a [u8],
    ) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
        map(
            take_while1(|c| !is_dollar(c) && !is_open_bracket(c)),
            |s: &[u8]| ParseResult::Single(Element::Text(slice_as_bytes(original, s))),
        )(input)
    }

    // HTML tag in complete mode - any tag that's NOT an ESI tag
    fn html_tag_complete<'a>(
        original: &Bytes,
        input: &'a [u8],
    ) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
        // Check that this is NOT an esi: tag
        let (_, _) = peek(tuple((open_bracket, not(tag(b"esi:")))))(input)?;

        // Parse the HTML tag (simplified - just capture until >)
        let (rest, html) = recognize(tuple((
            open_bracket,
            take_until(&[CLOSE_BRACKET][..]),
            close_bracket,
        )))(input)?;

        Ok((
            rest,
            ParseResult::Single(Element::Html(slice_as_bytes(original, html))),
        ))
    }

    // Parse content using complete parsers
    let mut elements = Vec::new();
    let mut remaining = content;

    while !remaining.is_empty() {
        // Try expression first (starts with $)
        if let Ok((rest, result)) = interpolated_expression(remaining) {
            result.append_to(&mut elements);
            remaining = rest;
            continue;
        }

        // Try HTML tag (starts with < but NOT <esi:)
        if let Ok((rest, result)) = html_tag_complete(original, remaining) {
            result.append_to(&mut elements);
            remaining = rest;
            continue;
        }

        // Try text (stops at $ or <)
        if let Ok((rest, result)) = text_complete(original, remaining) {
            result.append_to(&mut elements);
            remaining = rest;
            continue;
        }

        // Fallback: consume one byte as text if nothing else matches
        // This handles stray $ or < characters that aren't valid expressions/tags
        elements.push(Element::Text(slice_as_bytes(original, &remaining[..1])));
        remaining = &remaining[1..];
    }

    elements
}

fn esi_vars_long<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    // esi:vars supports nested ESI tags (like esi:assign) per common usage patterns
    let (input, _) = streaming_bytes::tag(b"<esi:vars>")(input)?;
    let (input, elements) = tag_content(original, input)?;
    let (input, _) = streaming_bytes::tag(b"</esi:vars>")(input)?;

    Ok((input, ParseResult::Multiple(elements)))
}

fn esi_comment(input: &[u8]) -> IResult<&[u8], ParseResult, Error<&[u8]>> {
    map(
        delimited(
            streaming_bytes::tag(b"<esi:comment"),
            attributes,
            preceded(streaming_char::multispace0, streaming_self_closing), // ESI comment must be self-closing per ESI spec
        ),
        |_| ParseResult::Empty,
    )(input)
}

/// Zero-copy esi:remove parser
/// Per ESI spec, esi:remove content is discarded - no nested ESI processing needed
fn esi_remove(input: &[u8]) -> IResult<&[u8], ParseResult, Error<&[u8]>> {
    let (input, _) = streaming_bytes::tag(b"<esi:remove>")(input)?;
    let (input, _) = streaming_bytes::take_until(b"</esi:remove>".as_ref())(input)?;
    let (input, _) = streaming_bytes::tag(b"</esi:remove>")(input)?;
    Ok((input, ParseResult::Empty))
}

fn esi_text<'a>(
    original: &Bytes,
    input: &'a [u8],
) -> IResult<&'a [u8], ParseResult, Error<&'a [u8]>> {
    map(
        delimited(
            streaming_bytes::tag(b"<esi:text>"),
            streaming_bytes::take_until(b"</esi:text>".as_ref()),
            streaming_bytes::tag(b"</esi:text>"),
        ),
        |v| ParseResult::Single(Element::Text(slice_as_bytes(original, v))),
    )(input)
}
fn esi_include(input: &[u8]) -> IResult<&[u8], ParseResult, Error<&[u8]>> {
    alt((esi_include_self_closing, esi_include_with_params))(input)
}

/// Helper to extract include attributes from the attributes `HashMap`
fn extract_include_attrs(mut attrs: HashMap<String, String>) -> IncludeAttributes {
    let src = parse_attr_as_expr(take_attr(&mut attrs, "src"));
    let alt = take_attr_opt(&mut attrs, "alt").map(parse_attr_as_expr);
    let continue_on_error = attrs.get("onerror").is_some_and(|s| s == "continue");
    let ttl = take_attr_opt(&mut attrs, "ttl");
    let maxwait = take_attr_opt(&mut attrs, "maxwait").and_then(|s| s.parse::<u32>().ok());
    let no_store = attrs
        .get("no-store")
        .is_some_and(|s| s == "on" || s == "true");
    let method = take_attr_opt(&mut attrs, "method").map(parse_attr_as_expr);
    let entity = take_attr_opt(&mut attrs, "entity").map(parse_attr_as_expr);

    // Parse header manipulation attributes
    let mut appendheaders = Vec::new();
    let mut setheaders = Vec::new();
    let mut removeheaders = Vec::new();

    // Collect all header attributes (there can be multiple)
    let keys: Vec<String> = attrs.keys().cloned().collect();
    for key in keys {
        if key.starts_with("appendheader") {
            if let Some(value) = attrs.remove(&key) {
                // Parse header format: "Header-Name: value"
                if let Some((name, val)) = value.split_once(':') {
                    appendheaders.push((
                        name.trim().to_string(),
                        parse_attr_as_expr(val.trim().to_string()),
                    ));
                }
            }
        } else if key.starts_with("setheader") {
            if let Some(value) = attrs.remove(&key) {
                if let Some((name, val)) = value.split_once(':') {
                    setheaders.push((
                        name.trim().to_string(),
                        parse_attr_as_expr(val.trim().to_string()),
                    ));
                }
            }
        } else if key.starts_with("removeheader") {
            if let Some(value) = attrs.remove(&key) {
                removeheaders.push(value);
            }
        }
    }

    IncludeAttributes {
        src,
        alt,
        continue_on_error,
        ttl,
        maxwait,
        no_store,
        method,
        entity,
        appendheaders,
        removeheaders,
        setheaders,
    }
}

fn esi_include_self_closing(input: &[u8]) -> IResult<&[u8], ParseResult, Error<&[u8]>> {
    map(
        delimited(
            streaming_bytes::tag(b"<esi:include"),
            attributes,
            preceded(streaming_char::multispace0, streaming_self_closing),
        ),
        |attrs| {
            let attrs = extract_include_attrs(attrs);

            ParseResult::Single(Element::Esi(Tag::Include {
                params: Vec::new(),
                attrs,
            }))
        },
    )(input)
}

fn esi_include_with_params(input: &[u8]) -> IResult<&[u8], ParseResult, Error<&[u8]>> {
    map(
        tuple((
            delimited(
                streaming_bytes::tag(b"<esi:include"),
                attributes,
                preceded(streaming_char::multispace0, streaming_close_bracket),
            ),
            many0(preceded(streaming_char::multispace0, esi_param)),
            preceded(
                streaming_char::multispace0,
                streaming_bytes::tag(&b"</esi:include>"[..]),
            ),
        )),
        |(attrs, params, _)| {
            let attrs = extract_include_attrs(attrs);

            ParseResult::Single(Element::Esi(Tag::Include { params, attrs }))
        },
    )(input)
}

fn esi_param(input: &[u8]) -> IResult<&[u8], (String, Expr), Error<&[u8]>> {
    map(
        delimited(
            streaming_bytes::tag(b"<esi:param"),
            attributes,
            preceded(
                streaming_char::multispace0,
                alt((streaming_close_bracket, streaming_self_closing)),
            ),
        ),
        |mut attrs| {
            let name = take_attr(&mut attrs, "name");
            let value = parse_attr_as_expr(take_attr(&mut attrs, "value"));
            (name, value)
        },
    )(input)
}

fn attributes(input: &[u8]) -> IResult<&[u8], HashMap<String, String>, Error<&[u8]>> {
    fold_many0(
        separated_pair(
            preceded(
                streaming_char::multispace1,
                // Allow alphanumeric characters and hyphens in attribute names
                streaming_bytes::take_while1(|c| {
                    (c as char).is_alphanumeric() || c == b'-' || c == b'_'
                }),
            ),
            streaming_bytes::tag(b"="),
            htmlstring,
        ),
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
            streaming_bytes::take_while(|c| !is_double_quote(c)),
            double_quote,
        ),
        delimited(
            single_quote,
            streaming_bytes::take_while(|c| !is_single_quote(c)),
            single_quote,
        ),
    ))(input)
}

// ============================================================================
// Zero-Copy HTML/Text Parsers
// ============================================================================
/// Helper to find and consume the closing '>' character
#[inline]
fn streaming_close_bracket(input: &[u8]) -> IResult<&[u8], &[u8], Error<&[u8]>> {
    streaming_bytes::tag(b">")(input)
}

/// Helper to find and consume the closing '>' character
#[inline]
fn close_bracket(input: &[u8]) -> IResult<&[u8], &[u8], Error<&[u8]>> {
    tag(b">")(input)
}

/// Helper to find and consume the closing self-closing tag characters '/>'
#[inline]
fn streaming_self_closing(input: &[u8]) -> IResult<&[u8], &[u8], Error<&[u8]>> {
    streaming_bytes::tag(b"/>")(input)
}

/// Helper to find and consume the opening '<' character
#[inline]
fn open_bracket(input: &[u8]) -> IResult<&[u8], &[u8], Error<&[u8]>> {
    tag(b"<")(input)
}

/// Helper to find and consume the opening '<' character
#[inline]
fn streaming_open_bracket(input: &[u8]) -> IResult<&[u8], &[u8], Error<&[u8]>> {
    streaming_bytes::tag(b"<")(input)
}

/// Helper to find and consume the closing double quote character
#[inline]
fn double_quote(input: &[u8]) -> IResult<&[u8], &[u8], Error<&[u8]>> {
    streaming_bytes::tag(b"\"")(input)
}

/// Helper to find and consume the closing single quote character
#[inline]
fn single_quote(input: &[u8]) -> IResult<&[u8], &[u8], Error<&[u8]>> {
    streaming_bytes::tag(b"\'")(input)
}

/// Check if byte is an opening bracket '<'
#[inline]
const fn is_close_bracket(b: u8) -> bool {
    b == CLOSE_BRACKET
}

/// Check if byte is a double quote '"'
#[inline]
const fn is_double_quote(b: u8) -> bool {
    b == DOUBLE_QUOTE
}

/// Check if byte is a single quote '\''
#[inline]
const fn is_single_quote(b: u8) -> bool {
    b == SINGLE_QUOTE
}

/// Check if byte can start an HTML/XML tag name (including special constructs like <!--, <!DOCTYPE, <![CDATA[)
#[inline]
const fn is_tag_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'!'
}

/// Check if byte can continue an HTML/XML tag name
#[inline]
const fn is_tag_cont(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.' | b':' | b'[')
}

/// Parse an HTML/XML-style tag name.
/// Returns the subslice of the original input containing only the tag name.
#[inline]
fn tag_name(input: &[u8]) -> IResult<&[u8], &[u8], Error<&[u8]>> {
    recognize(nom::sequence::pair(
        streaming_bytes::take_while_m_n(1, 1, is_tag_start), // first letter
        streaming_bytes::take_while(is_tag_cont),            // rest of name
    ))(input)
}

/// Parse a complete opening tag
/// Returns (`remaining_input`, (`tag_name`, `full_tag_slice`))
/// Only succeeds when we have a complete tag (ending with > or />)
#[allow(clippy::type_complexity)]
fn esi_opening_tag(input: &[u8]) -> IResult<&[u8], (&[u8], &[u8]), Error<&[u8]>> {
    let start = input;

    // Parse <tagname
    let (rest, _) = streaming_open_bracket(input)?;
    let (rest, name) = tag_name(rest)?;

    // Parse attributes - consume everything up to '>'
    let (rest, _) = streaming_bytes::take_till(is_close_bracket)(rest)?;

    // Must have > to be complete
    let (rest, _) = streaming_close_bracket(rest)?;

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
            let (rest, (name, start)) = esi_opening_tag(i)?;
            // Dispatch based on tag name without re-parsing
            match name {
                // ESI tags - pass start position to parse from <esi:tagname
                b"esi:assign" => esi_assign(original, start),
                b"esi:include" => esi_include(start),
                b"esi:vars" => esi_vars(original, start),
                b"esi:comment" => esi_comment(start),
                b"esi:remove" => esi_remove(start),
                b"esi:text" => esi_text(original, start),
                b"esi:choose" => esi_choose(original, start),
                b"esi:try" => esi_try(original, start),
                b"esi:when" => esi_when(original, start),
                b"esi:otherwise" => esi_otherwise(original, start),
                b"esi:attempt" => esi_attempt(original, start),
                b"esi:except" => esi_except(original, start),
                b"esi:foreach" => esi_foreach(original, start),
                b"esi:break" => esi_break(start),

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
    let start = input;
    let (rest, _) = delimited(
        streaming_bytes::tag(b"<!--"),
        streaming_bytes::take_until(b"-->".as_ref()),
        streaming_bytes::tag(b"-->"),
    )(input)?;
    let full_comment = &start[..start.len() - rest.len()];
    Ok((
        rest,
        ParseResult::Single(Element::Html(slice_as_bytes(original, full_comment))),
    ))
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
        streaming_bytes::tag_no_case(b"<script"),
        streaming_bytes::take_till(is_close_bracket),
        streaming_close_bracket,
    ))(input)?;

    // Parse content (if any) and closing tag (if any)
    let (input, _) = opt(tuple((
        script_content,
        recognize(delimited(
            streaming_bytes::tag_no_case(b"</script"),
            streaming_char::multispace0,
            streaming_close_bracket,
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
    let (_, _) = peek(not(streaming_bytes::tag(b"</esi:")))(input)?;

    map(
        recognize(tuple((
            streaming_bytes::tag(b"</"),
            tag_name,
            streaming_char::multispace0,
            streaming_close_bracket,
        ))),
        |s: &[u8]| ParseResult::Single(Element::Html(slice_as_bytes(original, s))),
    )(input)
}

// ============================================================================
// Byte Predicate Constants and Helpers
// ============================================================================

/// Common byte constants for parsing
const OPEN_BRACKET: u8 = b'<';
const CLOSE_BRACKET: u8 = b'>';
const DOLLAR: u8 = b'$';
const DOUBLE_QUOTE: u8 = b'"';
const SINGLE_QUOTE: u8 = b'\'';
const SLASH: u8 = b'/';
const EQUALS: u8 = b'=';

/// Check if byte is the opening bracket '<'
#[inline]
const fn is_open_bracket(b: u8) -> bool {
    b == OPEN_BRACKET
}

/// Check if byte is a dollar sign '$'
#[inline]
const fn is_dollar(b: u8) -> bool {
    b == DOLLAR
}
#[inline]
const fn is_alphanumeric_or_underscore(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

#[inline]
const fn is_lower_alphanumeric_or_underscore(c: u8) -> bool {
    c.is_ascii_lowercase() || c.is_ascii_digit() || c == b'_'
}

fn esi_fn_name(input: &[u8]) -> IResult<&[u8], String, Error<&[u8]>> {
    map(
        preceded(tag(b"$"), take_while1(is_lower_alphanumeric_or_underscore)),
        bytes_to_string,
    )(input)
}

fn esi_var_name(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    map(
        tuple((
            take_while1(is_alphanumeric_or_underscore),
            opt(delimited(tag(b"{"), esi_var_key_expr, tag(b"}"))),
            opt(preceded(tag(b"|"), fn_nested_argument)),
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
        take_while(|c| !is_dollar(c) && c != b'{' && c != b'}' && c != b',' && c != DOUBLE_QUOTE),
        bytes_to_string,
    )(input)
}

// TODO: handle escaping
fn single_quoted_string(input: &[u8]) -> IResult<&[u8], String, Error<&[u8]>> {
    map(
        delimited(tag(b"'"), take_while(|c| !is_single_quote(c)), tag(b"'")),
        bytes_to_string,
    )(input)
}
fn triple_quoted_string(input: &[u8]) -> IResult<&[u8], String, Error<&[u8]>> {
    map(
        delimited(tag(b"'''"), take_until("'''"), tag(b"'''")),
        bytes_to_string,
    )(input)
}

fn string(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    map(
        alt((triple_quoted_string, single_quoted_string)),
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
        triple_quoted_string,
        single_quoted_string,
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
        tuple((multispace0, tag(b","), multispace0)),
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
            opt(tag(b"-")),
            take_while1(|c: u8| c.is_ascii_digit()),
        ))),
        |s: &[u8]| String::from_utf8_lossy(s).parse::<i32>().map(Expr::Integer),
    )(input)
}

fn bareword(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    map(
        take_while1(is_alphanumeric_or_underscore),
        |name: &[u8]| Expr::Variable(bytes_to_string(name), None, None),
    )(input)
}

fn esi_function(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    let (input, parsed) = tuple((
        esi_fn_name,
        delimited(
            terminated(tag(b"("), multispace0),
            fn_argument,
            preceded(multispace0, tag(b")")),
        ),
    ))(input)?;

    let (name, args) = parsed;

    Ok((input, Expr::Call(name, args)))
}

fn esi_variable(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    delimited(tag(b"$("), esi_var_name, tag(b")"))(input)
}

/// Parse all binary operators
/// Per ESI spec: all operators at same precedence level, evaluated left-to-right
fn operator(input: &[u8]) -> IResult<&[u8], Operator, Error<&[u8]>> {
    alt((
        // Longer operators first to avoid partial matches
        map(tag(b"matches_i"), |_| Operator::MatchesInsensitive),
        map(tag(b"matches"), |_| Operator::Matches),
        map(tag(b"has_i"), |_| Operator::HasInsensitive),
        map(tag(b"has"), |_| Operator::Has),
        map(tag(b"=="), |_| Operator::Equals),
        map(tag(b"!="), |_| Operator::NotEquals),
        map(tag(b"<="), |_| Operator::LessThanOrEqual),
        map(tag(b">="), |_| Operator::GreaterThanOrEqual),
        map(tag(b"<"), |_| Operator::LessThan),
        map(tag(b">"), |_| Operator::GreaterThan),
        map(tag(b"&&"), |_| Operator::And),
        map(tag(b"||"), |_| Operator::Or),
        // Arithmetic operators (after comparison to avoid conflicts with <=, >=)
        map(tag(b"+"), |_| Operator::Add),
        map(tag(b"-"), |_| Operator::Subtract),
        map(tag(b"*"), |_| Operator::Multiply),
        map(tag(b"/"), |_| Operator::Divide),
        map(tag(b"%"), |_| Operator::Modulo),
    ))(input)
}

fn interpolated_expression(input: &[u8]) -> IResult<&[u8], ParseResult, Error<&[u8]>> {
    map(
        alt((
            dict_literal,
            list_literal,
            esi_function,
            esi_variable,
            integer,
            string,
        )),
        |expr| ParseResult::Single(Element::Expr(expr)),
    )(input)
}

fn dict_literal(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    map(
        delimited(
            tag(b"{"),
            separated_list0(
                tuple((multispace0, tag(b","), multispace0)),
                tuple((
                    delimited(multispace0, primary_expr, multispace0),
                    preceded(tag(b":"), delimited(multispace0, primary_expr, multispace0)),
                )),
            ),
            preceded(multispace0, tag(b"}")),
        ),
        Expr::DictLiteral,
    )(input)
}

fn list_literal(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    map(
        delimited(
            tag(b"["),
            separated_list0(
                tuple((multispace0, tag(b","), multispace0)),
                delimited(multispace0, primary_expr, multispace0),
            ),
            preceded(multispace0, tag(b"]")),
        ),
        Expr::ListLiteral,
    )(input)
}

/// Parse primary expressions (highest precedence atoms)
/// Handles: variables, functions, literals, grouped expressions
fn primary_expr(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    alt((
        // Parse grouped expression: (expr)
        delimited(
            tag(b"("),
            delimited(multispace0, expr, multispace0),
            tag(b")"),
        ),
        // Parse dictionary literal: {key:value, key:value}
        dict_literal,
        // Parse list literal: [value, value]
        list_literal,
        // Parse basic expressions
        esi_function,
        esi_variable,
        integer,
        string,
    ))(input)
}

/// Entry point for expression parsing
///
/// Per ESI spec: "Operands associate from left to right"
/// All operators at same precedence, evaluated left-to-right
/// Format: `unary_expr` (operator `unary_expr`)*
/// Left-associative: A op B op C → (A op B) op C
fn expr(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    let (input, first) = unary_expr(input)?;

    fold_many0(
        tuple((delimited(multispace0, operator, multispace0), unary_expr)),
        move || first.clone(),
        |left, (op, right)| Expr::Comparison {
            left: Box::new(left),
            operator: op,
            right: Box::new(right),
        },
    )(input)
}

/// Parse unary expressions (!, highest precedence for operators)
///
/// Format: ! `unary_expr` | `primary_expr`
/// Handles negation recursively (supports !!expr, !!!expr, etc.)
fn unary_expr(input: &[u8]) -> IResult<&[u8], Expr, Error<&[u8]>> {
    alt((
        // Parse negation: !expr (recursively handles multiple !)
        map(
            preceded(tag(b"!"), preceded(multispace0, unary_expr)),
            |expr| Expr::Not(Box::new(expr)),
        ),
        // Otherwise parse primary expression
        primary_expr,
    ))(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_choose() {
        let input = b"<esi:choose></esi:choose>";
        let bytes = Bytes::from_static(input);
        let result = parse_remainder(&bytes);
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
        let result = parse_remainder(&bytes);
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
        let result = parse_remainder(&bytes);
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
        // esi_vars returns Single when parsing short form with expression
        match x {
            ParseResult::Single(Element::Expr(Expr::Variable(name, None, None))) => {
                assert_eq!(name, "hello");
            }
            ParseResult::Single(e) => {
                panic!("Expected Variable expression, got {:?}", e);
            }
            ParseResult::Multiple(_) => {
                panic!("Expected ParseResult::Single, got Multiple");
            }
            ParseResult::Empty => {
                panic!("Expected ParseResult::Single, got Empty");
            }
        }
    }
    #[test]
    fn test_parse_esi_vars_long() {
        // <esi:vars> can contain text, expressions, HTML, and nested ESI tags (like <esi:assign>)
        let input = br#"<esi:vars>hello<br></esi:vars>"#;
        let bytes = Bytes::from_static(input);
        let (rest, x) = parse_remainder(&bytes).unwrap();
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
        let (rest, elements) = parse_remainder(&bytes).unwrap();

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
    fn test_vars_with_expressions() {
        // This is the proper use of esi:vars - text with expressions
        let input = br#"<esi:vars>Hello $(name), welcome!</esi:vars>"#;
        let bytes = Bytes::from_static(input);
        let (rest, elements) = parse_remainder(&bytes).unwrap();

        assert_eq!(rest.len(), 0, "Should parse completely");
        assert_eq!(elements.len(), 3);
        assert!(matches!(&elements[0], Element::Text(t) if t.as_ref() == b"Hello "));
        assert!(matches!(&elements[1], Element::Expr(_)));
        assert!(matches!(&elements[2], Element::Text(t) if t.as_ref() == b", welcome!"));
    }

    #[test]
    fn test_assign_inside_vars() {
        // Per ESI spec, <esi:vars> can contain <esi:assign> tags
        let input = br#"
<esi:vars>
    <esi:assign name="xyz" value="'test'" />
    Result: $(xyz)
</esi:vars>"#;
        let bytes = Bytes::from_static(input);
        let (rest, elements) = parse_remainder(&bytes).unwrap();

        assert_eq!(rest.len(), 0, "Should parse completely");

        // Should have: whitespace, assign tag, whitespace, text "Result: ", expression $(xyz), whitespace
        assert!(
            elements.len() >= 3,
            "Should have at least assign tag, text, and expression"
        );

        // Find the assign tag
        let has_assign = elements
            .iter()
            .any(|e| matches!(e, Element::Esi(Tag::Assign { name, .. }) if name == "xyz"));
        assert!(has_assign, "Should contain esi:assign tag with name='xyz'");

        // Find the expression
        let has_expr = elements
            .iter()
            .any(|e| matches!(e, Element::Expr(Expr::Variable(name, None, None)) if name == "xyz"));
        assert!(has_expr, "Should contain expression $(xyz)");
    }

    #[test]
    fn test_parse_complex_expr() {
        let input = br#"<esi:vars name="$call('hello') matches $(var{'key'})"/>"#;
        let bytes = Bytes::from_static(input);
        let (rest, x) = parse_remainder(&bytes).unwrap();
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
        let (rest, elements) = parse_remainder(&bytes).unwrap();
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
        let (rest, _elements) = parse_remainder(&bytes).unwrap();
        assert_eq!(rest.len(), 0);
    }

    #[test]
    fn test_parse_plain_text() {
        let input = b"hello\nthere";
        let bytes = Bytes::from_static(input);
        let (rest, x) = parse_remainder(&bytes).unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(x, [Element::Text(Bytes::from_static(b"hello\nthere"))]);
    }
    #[test]
    fn test_parse_interpolated() {
        let input = b"hello $(foo)<esi:vars>goodbye $(foo)</esi:vars>";
        let bytes = Bytes::from_static(input);
        let (rest, x) = parse_remainder(&bytes).unwrap();
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
        let (rest, _) = parse_remainder(&bytes).unwrap();
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
        let result1 = parse_remainder(&bytes1);
        assert!(
            result1.is_ok(),
            "Should parse < operator: {:?}",
            result1.err()
        );

        let input2 = b"<esi:choose><esi:when test=\"$(count) >= 5\">yes</esi:when></esi:choose>";
        let bytes2 = Bytes::from_static(input2);
        let result2 = parse_remainder(&bytes2);
        assert!(
            result2.is_ok(),
            "Should parse >= operator: {:?}",
            result2.err()
        );

        // Test has operator
        let input3 = b"<esi:choose><esi:when test=\"$(USER_AGENT) has 'Mobile'\">yes</esi:when></esi:choose>";
        let bytes3 = Bytes::from_static(input3);
        let result3 = parse_remainder(&bytes3);
        assert!(
            result3.is_ok(),
            "Should parse 'has' operator: {:?}",
            result3.err()
        );

        // Test has_i operator
        let input4 =
            b"<esi:choose><esi:when test=\"$(COOKIE) has_i 'sam'\">yes</esi:when></esi:choose>";
        let bytes4 = Bytes::from_static(input4);
        let result4 = parse_remainder(&bytes4);
        assert!(
            result4.is_ok(),
            "Should parse 'has_i' operator: {:?}",
            result4.err()
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
        let (rest, elements) = parse_remainder(&bytes).unwrap();
        assert_eq!(rest.len(), 0, "Should parse completely");
        assert_eq!(elements.len(), 1);
        if let Element::Esi(Tag::Include { attrs, .. }) = &elements[0] {
            assert!(
                matches!(&attrs.src, Expr::String(Some(s)) if s == "http://example.com/fragment")
            );
        } else {
            panic!("Expected Include tag");
        }

        // Test mixed quotes
        let input2 = b"<esi:assign name='foo' value=\"bar\" />";
        let bytes2 = Bytes::from_static(input2);
        let (rest, elements) = parse_remainder(&bytes2).unwrap();
        assert_eq!(rest.len(), 0, "Should parse completely");
        assert_eq!(elements.len(), 1);
        if let Element::Esi(Tag::Assign {
            name,
            subscript: _,
            value,
        }) = &elements[0]
        {
            assert_eq!(name, "foo");
            assert_eq!(value, &Expr::String(Some("bar".to_string())));
        } else {
            panic!("Expected Assign tag");
        }
    }

    #[test]
    fn test_assign_valid_variable_names() {
        // Valid names
        let valid_cases: Vec<&[u8]> = vec![
            b"<esi:assign name=\"valid_name\" value=\"test\"/>",
            b"<esi:assign name=\"a\" value=\"test\"/>",
            b"<esi:assign name=\"Z\" value=\"test\"/>",
            b"<esi:assign name=\"var123\" value=\"test\"/>",
            b"<esi:assign name=\"my_var_123\" value=\"test\"/>",
            b"<esi:assign name=\"CamelCase\" value=\"test\"/>",
        ];

        for input in valid_cases {
            let bytes = Bytes::copy_from_slice(input);
            let result = parse_remainder(&bytes);
            assert!(
                result.is_ok(),
                "Should parse valid name: {:?}",
                std::str::from_utf8(input)
            );
            let (_, elements) = result.unwrap();
            let has_assign = elements
                .iter()
                .any(|e| matches!(e, Element::Esi(Tag::Assign { .. })));
            assert!(
                has_assign,
                "Should have Assign tag for: {:?}",
                std::str::from_utf8(input)
            );
        }
    }

    #[test]
    fn test_assign_invalid_variable_names() {
        // Invalid names should be rejected (treated as empty/skipped)
        let invalid_cases: Vec<&[u8]> = vec![
            b"<esi:assign name=\"$invalid\" value=\"test\"/>", // starts with $
            b"<esi:assign name=\"123invalid\" value=\"test\"/>", // starts with digit
            b"<esi:assign name=\"_invalid\" value=\"test\"/>", // starts with underscore
            b"<esi:assign name=\"invalid-name\" value=\"test\"/>", // contains dash
            b"<esi:assign name=\"invalid.name\" value=\"test\"/>", // contains dot
            b"<esi:assign name=\"invalid name\" value=\"test\"/>", // contains space
            b"<esi:assign name=\"\" value=\"test\"/>",         // empty name
        ];

        for input in invalid_cases {
            let bytes = Bytes::copy_from_slice(input);
            let result = parse_remainder(&bytes);
            assert!(
                result.is_ok(),
                "Should parse (but skip invalid): {:?}",
                std::str::from_utf8(input)
            );
            let (_, elements) = result.unwrap();
            let has_assign = elements
                .iter()
                .any(|e| matches!(e, Element::Esi(Tag::Assign { .. })));
            assert!(
                !has_assign,
                "Should NOT have Assign tag for invalid name: {:?}",
                std::str::from_utf8(input)
            );
        }
    }

    #[test]
    fn test_assign_name_length_limit() {
        // Test 256 character limit
        let valid_256 = format!(r#"<esi:assign name="a{}" value="test"/>"#, "b".repeat(255));
        let bytes = Bytes::from(valid_256.clone());
        let result = parse_remainder(&bytes);
        assert!(result.is_ok(), "Should parse 256 char name");
        let (_, elements) = result.unwrap();
        let has_assign = elements
            .iter()
            .any(|e| matches!(e, Element::Esi(Tag::Assign { .. })));
        assert!(has_assign, "Should have Assign tag for 256 char name");

        // Test 257 characters (should be invalid)
        let invalid_257 = format!(r#"<esi:assign name="a{}" value="test"/>"#, "b".repeat(256));
        let bytes = Bytes::from(invalid_257);
        let result = parse_remainder(&bytes);
        assert!(result.is_ok(), "Should parse (but skip)");
        let (_, elements) = result.unwrap();
        let has_assign = elements
            .iter()
            .any(|e| matches!(e, Element::Esi(Tag::Assign { .. })));
        assert!(!has_assign, "Should NOT have Assign tag for 257 char name");
    }

    #[test]
    fn test_assign_long_form_invalid_name() {
        // Long form with invalid name should also be rejected
        let input = b"<esi:assign name=\"$invalid\">test value</esi:assign>";
        let bytes = Bytes::copy_from_slice(input);
        let result = parse_remainder(&bytes);
        assert!(result.is_ok(), "Should parse");
        let (_, elements) = result.unwrap();
        let has_assign = elements
            .iter()
            .any(|e| matches!(e, Element::Esi(Tag::Assign { .. })));
        assert!(
            !has_assign,
            "Should NOT have Assign tag for invalid name in long form"
        );
    }

    #[test]
    fn test_assign_with_subscript() {
        // Test subscript assignment parsing with bare identifier
        let input = b"<esi:assign name=\"ages{joan}\" value=\"28\"/>";
        let bytes = Bytes::copy_from_slice(input);
        let result = parse_remainder(&bytes);
        assert!(result.is_ok(), "Should parse");
        let (_, elements) = result.unwrap();
        assert_eq!(elements.len(), 1);

        match &elements[0] {
            Element::Esi(Tag::Assign {
                name,
                subscript,
                value,
            }) => {
                assert_eq!(name, "ages");
                assert!(subscript.is_some(), "Should have subscript");
                if let Some(sub) = subscript {
                    // Should be a string literal "joan"
                    assert!(matches!(sub, Expr::String(Some(s)) if s == "joan"));
                }
                assert!(matches!(value, Expr::Integer(28)));
            }
            _ => panic!("Expected Assign tag"),
        }

        // Test with another bare identifier
        let input2 = b"<esi:assign name=\"ages{bob}\" value=\"34\"/>";
        let bytes2 = Bytes::copy_from_slice(input2);
        let result2 = parse_remainder(&bytes2);
        assert!(result2.is_ok(), "Should parse");
        let (_, elements2) = result2.unwrap();
        assert_eq!(elements2.len(), 1);

        match &elements2[0] {
            Element::Esi(Tag::Assign {
                name,
                subscript,
                value,
            }) => {
                assert_eq!(name, "ages");
                assert!(subscript.is_some(), "Should have subscript");
                if let Some(sub) = subscript {
                    // Should be a string literal "bob"
                    assert!(
                        matches!(sub, Expr::String(Some(s)) if s == "bob"),
                        "Subscript should be 'bob', got {:?}",
                        sub
                    );
                }
                assert!(matches!(value, Expr::Integer(34)));
            }
            _ => panic!("Expected Assign tag"),
        }
    }

    #[test]
    fn test_assign_with_quoted_subscript() {
        // Test ESI spec-compliant subscript with quoted strings in assignment
        let input = b"<esi:assign name=\"ages{'joan'}\" value=\"28\"/>";
        let bytes = Bytes::copy_from_slice(input);
        let result = parse_remainder(&bytes);

        assert!(
            result.is_ok(),
            "Should parse spec-compliant quoted subscript"
        );
        let (_, elements) = result.unwrap();
        assert_eq!(elements.len(), 1, "Should have exactly 1 element");

        match &elements[0] {
            Element::Esi(Tag::Assign {
                name,
                subscript,
                value,
            }) => {
                assert_eq!(name, "ages");
                assert!(subscript.is_some(), "Should have subscript");
                if let Some(sub) = subscript {
                    // Should be a string literal "joan"
                    assert!(
                        matches!(sub, Expr::String(Some(s)) if s == "joan"),
                        "Subscript should be 'joan', got {:?}",
                        sub
                    );
                }
                assert!(matches!(value, Expr::Integer(28)));
            }
            other => panic!("Expected Assign tag, got {:?}", other),
        }

        // Test with multiple quoted subscripts
        let input2 = b"<esi:assign name=\"data{'key1'}\" value=\"${'value1'}\"/>";
        let bytes2 = Bytes::copy_from_slice(input2);
        let result2 = parse_remainder(&bytes2);
        assert!(
            result2.is_ok(),
            "Should parse assignment with quoted subscript and quoted value"
        );
    }

    #[test]
    fn test_unclosed_script_tag() {
        // Unclosed script tag - should handle gracefully
        let input = b"<script>content without closing";
        let bytes = Bytes::from_static(input);
        let (rest, elements) = parse_remainder(&bytes).unwrap();

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
    #[test]
    fn test_html_comment() {
        let input = b"<!-- this is a comment -->";
        let bytes = Bytes::from_static(input);
        let (rest, elements) = parse_remainder(&bytes).unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(elements.len(), 1);
        // Should return full comment including delimiters
        assert!(matches!(
            &elements[0],
            Element::Html(h) if h.as_ref() == b"<!-- this is a comment -->"
        ));
    }

    #[test]
    fn test_parse_foreach() {
        let input = b"<esi:foreach collection=\"items\" item=\"x\">Item: $(x)</esi:foreach>";
        let bytes = Bytes::from_static(input);
        let (rest, elements) = parse_remainder(&bytes).unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(elements.len(), 1);

        match &elements[0] {
            Element::Esi(Tag::Foreach {
                collection,
                item,
                content,
            }) => {
                assert!(matches!(collection, Expr::Variable(name, None, None) if name == "items"));
                assert_eq!(item.as_deref(), Some("x"));
                assert!(!content.is_empty());
            }
            other => panic!("Expected Foreach tag, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_foreach_no_item() {
        let input = b"<esi:foreach collection=\"mylist\">Value: $(item)</esi:foreach>";
        let bytes = Bytes::from_static(input);
        let (rest, elements) = parse_remainder(&bytes).unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(elements.len(), 1);

        match &elements[0] {
            Element::Esi(Tag::Foreach {
                collection,
                item,
                content,
            }) => {
                assert!(matches!(collection, Expr::Variable(name, None, None) if name == "mylist"));
                assert_eq!(item, &None);
                assert!(!content.is_empty());
            }
            other => panic!("Expected Foreach tag, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_break() {
        let input = b"<esi:break />";
        let bytes = Bytes::from_static(input);
        let (rest, elements) = parse_remainder(&bytes).unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(elements.len(), 1);
        assert!(matches!(&elements[0], Element::Esi(Tag::Break)));
    }

    #[test]
    fn test_parse_foreach_with_break() {
        let input = b"<esi:foreach collection=\"items\"><esi:break /></esi:foreach>";
        let bytes = Bytes::from_static(input);
        let (rest, elements) = parse_remainder(&bytes).unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(elements.len(), 1);

        match &elements[0] {
            Element::Esi(Tag::Foreach {
                collection,
                content,
                ..
            }) => {
                assert!(matches!(collection, Expr::Variable(name, None, None) if name == "items"));
                assert_eq!(content.len(), 1);
                assert!(matches!(&content[0], Element::Esi(Tag::Break)));
            }
            other => panic!("Expected Foreach tag, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_dict_literal() {
        let input = b"{1:'apple',2:'orange'}";
        let result = dict_literal(input);
        assert!(result.is_ok(), "Dict literal should parse: {:?}", result);
        let (rest, expr) = result.unwrap();
        assert_eq!(rest, b"");
        assert!(matches!(expr, Expr::DictLiteral(_)));
    }

    #[test]
    fn test_left_to_right_evaluation() {
        // Test 1: Left-to-right evaluation per ESI spec
        // $(a) && $(b) || $(c) should parse as ($(a) && $(b)) || $(c)
        let input = b"$(a) && $(b) || $(c)";
        let result = expr(input);
        assert!(
            result.is_ok(),
            "Failed to parse '$(a) && $(b) || $(c)': {:?}",
            result
        );
        let (rest, parsed) = result.unwrap();
        assert_eq!(rest, b"");

        // Should have OR at the top level (last operator evaluated)
        match parsed {
            Expr::Comparison {
                operator: Operator::Or,
                left,
                right,
            } => {
                // Left should be: $(a) && $(b) (evaluated first, left-to-right)
                match *left {
                    Expr::Comparison {
                        operator: Operator::And,
                        ..
                    } => {}
                    _ => panic!("Expected AND on left side, got {:?}", left),
                }
                // Right should be: $(c)
                match *right {
                    Expr::Variable(name, None, None) if name == "c" => {}
                    _ => panic!("Expected variable 'c' on right side, got {:?}", right),
                }
            }
            _ => panic!("Expected OR at top level, got {:?}", parsed),
        }

        // Test 2: $(a) || $(b) && $(c) should parse as ($(a) || $(b)) && $(c) [left-to-right]
        let input = b"$(a) || $(b) && $(c)";
        let result = expr(input);
        assert!(result.is_ok(), "Failed to parse '$(a) || $(b) && $(c)'");
        let (rest, parsed) = result.unwrap();
        assert_eq!(rest, b"");

        // Should have AND at the top level (last operator, left-to-right)
        match parsed {
            Expr::Comparison {
                operator: Operator::And,
                left,
                right,
            } => {
                // Left should be: $(a) || $(b) (evaluated first)
                match *left {
                    Expr::Comparison {
                        operator: Operator::Or,
                        ..
                    } => {}
                    _ => panic!("Expected OR on left side, got {:?}", left),
                }
                // Right should be: $(c)
                match *right {
                    Expr::Variable(name, None, None) if name == "c" => {}
                    _ => panic!("Expected variable 'c' on right side, got {:?}", right),
                }
            }
            _ => panic!("Expected AND at top level, got {:?}", parsed),
        }

        // Test 3: Unary NOT binds tighter than binary operators
        // !$(a) && $(b) should parse as (!$(a)) && $(b)
        let input = b"!$(a) && $(b)";
        let result = expr(input);
        assert!(result.is_ok(), "Failed to parse '!$(a) && $(b)'");
        let (rest, parsed) = result.unwrap();
        assert_eq!(rest, b"");

        // Should have AND at the top level
        match parsed {
            Expr::Comparison {
                operator: Operator::And,
                left,
                right,
            } => {
                // Left should be: !$(a)
                match *left {
                    Expr::Not(_) => {}
                    _ => panic!("Expected NOT on left side, got {:?}", left),
                }
                // Right should be: $(b)
                match *right {
                    Expr::Variable(name, None, None) if name == "b" => {}
                    _ => panic!("Expected variable 'b' on right side, got {:?}", right),
                }
            }
            _ => panic!("Expected AND at top level, got {:?}", parsed),
        }

        // Test 4: Left-to-right with multiple operators
        // $(a) == $(b) || $(c) should parse as ($(a) == $(b)) || $(c)
        let input = b"$(a) == $(b) || $(c)";
        let result = expr(input);
        assert!(result.is_ok(), "Failed to parse '$(a) == $(b) || $(c)'");
        let (rest, parsed) = result.unwrap();
        assert_eq!(rest, b"");

        // Should have OR at the top level (last operator)
        match parsed {
            Expr::Comparison {
                operator: Operator::Or,
                left,
                right,
            } => {
                // Left should be: $(a) == $(b)
                match *left {
                    Expr::Comparison {
                        operator: Operator::Equals,
                        ..
                    } => {}
                    _ => panic!("Expected EQUALS on left side, got {:?}", left),
                }
                // Right should be: $(c)
                match *right {
                    Expr::Variable(name, None, None) if name == "c" => {}
                    _ => panic!("Expected variable 'c' on right side, got {:?}", right),
                }
            }
            _ => panic!("Expected OR at top level, got {:?}", parsed),
        }

        // Test 5: Parentheses override left-to-right evaluation
        // $(a) && ($(b) || $(c)) should respect the parentheses
        let input = b"$(a) && ($(b) || $(c))";
        let result = expr(input);
        assert!(result.is_ok(), "Failed to parse '$(a) && ($(b) || $(c))'");
        let (rest, parsed) = result.unwrap();
        assert_eq!(rest, b"");

        // Should have AND at the top level
        match parsed {
            Expr::Comparison {
                operator: Operator::And,
                left,
                right,
            } => {
                // Left should be: $(a)
                match *left {
                    Expr::Variable(name, None, None) if name == "a" => {}
                    _ => panic!("Expected variable 'a' on left side, got {:?}", left),
                }
                // Right should be: $(b) || $(c) (grouped by parentheses)
                match *right {
                    Expr::Comparison {
                        operator: Operator::Or,
                        ..
                    } => {}
                    _ => panic!("Expected OR on right side, got {:?}", right),
                }
            }
            _ => panic!("Expected AND at top level, got {:?}", parsed),
        }
    }

    #[test]
    fn test_arithmetic_left_to_right() {
        // Test 1: Per ESI spec, left-to-right evaluation
        // 2 + 3 * 4 should parse as (2 + 3) * 4 = 20 (not 14 like traditional math)
        let input = b"2 + 3 * 4";
        let result = expr(input);
        assert!(result.is_ok(), "Failed to parse '2 + 3 * 4': {:?}", result);
        let (rest, parsed) = result.unwrap();
        assert_eq!(rest, b"");

        // Should have * at the top level (last operator, left-to-right)
        match parsed {
            Expr::Comparison {
                operator: Operator::Multiply,
                left,
                right,
            } => {
                // Left should be: 2 + 3 (evaluated first)
                match *left {
                    Expr::Comparison {
                        operator: Operator::Add,
                        ..
                    } => {}
                    _ => panic!("Expected ADD on left side, got {:?}", left),
                }
                // Right should be: 4
                match *right {
                    Expr::Integer(4) => {}
                    _ => panic!("Expected integer 4 on right side, got {:?}", right),
                }
            }
            _ => panic!("Expected MULTIPLY at top level, got {:?}", parsed),
        }

        // Test 2: Subtraction and division
        // 10 - 2 / 2 should parse as (10 - 2) / 2 = 4 (not 9)
        let input = b"10 - 2 / 2";
        let result = expr(input);
        assert!(result.is_ok(), "Failed to parse '10 - 2 / 2'");
        let (rest, parsed) = result.unwrap();
        assert_eq!(rest, b"");

        // Should have / at the top level
        match parsed {
            Expr::Comparison {
                operator: Operator::Divide,
                left,
                right,
            } => {
                // Left should be: 10 - 2
                match *left {
                    Expr::Comparison {
                        operator: Operator::Subtract,
                        ..
                    } => {}
                    _ => panic!("Expected SUBTRACT on left side, got {:?}", left),
                }
                // Right should be: 2
                match *right {
                    Expr::Integer(2) => {}
                    _ => panic!("Expected integer 2 on right side, got {:?}", right),
                }
            }
            _ => panic!("Expected DIVIDE at top level, got {:?}", parsed),
        }

        // Test 3: Modulo
        // 7 + 3 % 2 should parse as (7 + 3) % 2 = 0
        let input = b"7 + 3 % 2";
        let result = expr(input);
        assert!(result.is_ok(), "Failed to parse '7 + 3 % 2'");
        let (rest, parsed) = result.unwrap();
        assert_eq!(rest, b"");

        // Should have % at the top level
        match parsed {
            Expr::Comparison {
                operator: Operator::Modulo,
                ..
            } => {}
            _ => panic!("Expected MODULO at top level, got {:?}", parsed),
        }

        // Test 4: Parentheses override left-to-right
        // 2 + (3 * 4) should respect parentheses = 2 + 12 = 14
        let input = b"2 + (3 * 4)";
        let result = expr(input);
        assert!(result.is_ok(), "Failed to parse '2 + (3 * 4)'");
        let (rest, parsed) = result.unwrap();
        assert_eq!(rest, b"");

        // Should have + at the top level
        match parsed {
            Expr::Comparison {
                operator: Operator::Add,
                left,
                right,
            } => {
                // Left should be: 2
                match *left {
                    Expr::Integer(2) => {}
                    _ => panic!("Expected integer 2 on left side, got {:?}", left),
                }
                // Right should be: 3 * 4 (grouped by parentheses)
                match *right {
                    Expr::Comparison {
                        operator: Operator::Multiply,
                        ..
                    } => {}
                    _ => panic!("Expected MULTIPLY on right side, got {:?}", right),
                }
            }
            _ => panic!("Expected ADD at top level, got {:?}", parsed),
        }

        // Test 5: Parentheses override left-to-right
        // 2 + (3 * 4) should respect parentheses = 2 + 12 = 14
        let input = b"2 + (3 * 4)";
        let result = expr(input);
        assert!(result.is_ok(), "Failed to parse '2 + (3 * 4)'");
        let (rest, parsed) = result.unwrap();
        assert_eq!(rest, b"");

        // Should have + at the top level
        match parsed {
            Expr::Comparison {
                operator: Operator::Add,
                left,
                right,
            } => {
                // Left should be: 2
                match *left {
                    Expr::Integer(2) => {}
                    _ => panic!("Expected integer 2 on left side, got {:?}", left),
                }
                // Right should be: 3 * 4 (grouped by parentheses)
                match *right {
                    Expr::Comparison {
                        operator: Operator::Multiply,
                        ..
                    } => {}
                    _ => panic!("Expected MULTIPLY on right side, got {:?}", right),
                }
            }
            _ => panic!("Expected ADD at top level, got {:?}", parsed),
        }

        // Test 6: Arithmetic mixed with comparison
        // 5 + 3 > 7 should parse as (5 + 3) > 7 = true
        let input = b"5 + 3 > 7";
        let result = expr(input);
        assert!(result.is_ok(), "Failed to parse '5 + 3 > 7'");
        let (rest, parsed) = result.unwrap();
        assert_eq!(rest, b"");

        // Should have > at the top level (last operator)
        match parsed {
            Expr::Comparison {
                operator: Operator::GreaterThan,
                left,
                right,
            } => {
                // Left should be: 5 + 3
                match *left {
                    Expr::Comparison {
                        operator: Operator::Add,
                        ..
                    } => {}
                    _ => panic!("Expected ADD on left side, got {:?}", left),
                }
                // Right should be: 7
                match *right {
                    Expr::Integer(7) => {}
                    _ => panic!("Expected integer 7 on right side, got {:?}", right),
                }
            }
            _ => panic!("Expected GREATER_THAN at top level, got {:?}", parsed),
        }
    }
}
