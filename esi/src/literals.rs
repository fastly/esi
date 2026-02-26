//! Byte and string literal constants for ESI parsing
//!
//! # Constant Types
//!
//! - `u8` constants: Used for direct byte comparisons and pattern matching
//!   (e.g., `c == COMMA`, `matches!(b, DOT | COLON)`)
//!
//! - `&[u8]` constants: Used with nom's `tag()` parser for matching sequences
//!   (e.g., `tag(EQUALS)`, `tag(VAR_OPEN)`)
//!
//! Single-byte constants are defined as `u8` if used primarily in comparisons,
//! or as `&[u8]` if used only with `tag()`. This avoids unnecessary `&[...]`
//! wrapping in the parser code.

// ============================================================================
// Basic Character Constants
// ============================================================================

pub const UNDERSCORE: u8 = b'_';
pub const HYPHEN: u8 = b'-';
pub const DOT: u8 = b'.';
pub const DOLLAR: u8 = b'$';
pub const EXCLAMATION: u8 = b'!';

// ============================================================================
// Tag & Bracket Delimiters
// ============================================================================

// Single-byte delimiters
pub const OPEN_BRACKET: u8 = b'<';
pub const CLOSE_BRACKET: u8 = b'>';

// Multi-byte tag sequences
pub const TAG_SELF_CLOSE: &[u8] = b"/>";
pub const TAG_OPEN_CLOSE: &[u8] = b"</";

// HTML tag sequences
pub const TAG_SCRIPT_OPEN: &[u8] = b"<script";
pub const TAG_SCRIPT_CLOSE: &[u8] = b"</script";

// HTML comment delimiters
pub const HTML_COMMENT_OPEN: &[u8] = b"<!--";
pub const HTML_COMMENT_CLOSE: &[u8] = b"-->";

// ============================================================================
// ESI Tag Sequences
// ============================================================================

// ESI opening tags
pub const TAG_ESI_ASSIGN_OPEN: &[u8] = b"<esi:assign";
pub const TAG_ESI_INCLUDE_OPEN: &[u8] = b"<esi:include";
pub const TAG_ESI_VARS_OPEN: &[u8] = b"<esi:vars";
pub const TAG_ESI_VARS_OPEN_COMPLETE: &[u8] = b"<esi:vars>";
pub const TAG_ESI_COMMENT_OPEN: &[u8] = b"<esi:comment";
pub const TAG_ESI_REMOVE_OPEN: &[u8] = b"<esi:remove>";
pub const TAG_ESI_TEXT_OPEN: &[u8] = b"<esi:text>";
pub const TAG_ESI_CHOOSE_OPEN: &[u8] = b"<esi:choose>";
pub const TAG_ESI_TRY_OPEN: &[u8] = b"<esi:try>";
pub const TAG_ESI_WHEN_OPEN: &[u8] = b"<esi:when";
pub const TAG_ESI_OTHERWISE_OPEN: &[u8] = b"<esi:otherwise>";
pub const TAG_ESI_ATTEMPT_OPEN: &[u8] = b"<esi:attempt>";
pub const TAG_ESI_EXCEPT_OPEN: &[u8] = b"<esi:except>";
pub const TAG_ESI_FOREACH_OPEN: &[u8] = b"<esi:foreach";
pub const TAG_ESI_BREAK_OPEN: &[u8] = b"<esi:break";
pub const TAG_ESI_PARAM_OPEN: &[u8] = b"<esi:param";

// ESI closing tags
pub const TAG_ESI_ASSIGN_CLOSE: &[u8] = b"</esi:assign>";
pub const TAG_ESI_INCLUDE_CLOSE: &[u8] = b"</esi:include>";
pub const TAG_ESI_VARS_CLOSE: &[u8] = b"</esi:vars>";
pub const TAG_ESI_TEXT_CLOSE: &[u8] = b"</esi:text>";
pub const TAG_ESI_CHOOSE_CLOSE: &[u8] = b"</esi:choose>";
pub const TAG_ESI_TRY_CLOSE: &[u8] = b"</esi:try>";
pub const TAG_ESI_WHEN_CLOSE: &[u8] = b"</esi:when>";
pub const TAG_ESI_OTHERWISE_CLOSE: &[u8] = b"</esi:otherwise>";
pub const TAG_ESI_ATTEMPT_CLOSE: &[u8] = b"</esi:attempt>";
pub const TAG_ESI_EXCEPT_CLOSE: &[u8] = b"</esi:except>";
pub const TAG_ESI_FOREACH_CLOSE: &[u8] = b"</esi:foreach>";
pub const TAG_ESI_REMOVE_CLOSE: &[u8] = b"</esi:remove>";

// ESI prefix for detection
pub const ESI_PREFIX: &[u8] = b"esi:";
pub const ESI_CLOSE_PREFIX: &[u8] = b"</esi:";

// ESI tag names (for dispatcher matching)
pub const TAG_NAME_ESI_ASSIGN: &[u8] = b"esi:assign";
pub const TAG_NAME_ESI_INCLUDE: &[u8] = b"esi:include";
pub const TAG_NAME_ESI_VARS: &[u8] = b"esi:vars";
pub const TAG_NAME_ESI_COMMENT: &[u8] = b"esi:comment";
pub const TAG_NAME_ESI_REMOVE: &[u8] = b"esi:remove";
pub const TAG_NAME_ESI_TEXT: &[u8] = b"esi:text";
pub const TAG_NAME_ESI_CHOOSE: &[u8] = b"esi:choose";
pub const TAG_NAME_ESI_TRY: &[u8] = b"esi:try";
pub const TAG_NAME_ESI_WHEN: &[u8] = b"esi:when";
pub const TAG_NAME_ESI_OTHERWISE: &[u8] = b"esi:otherwise";
pub const TAG_NAME_ESI_ATTEMPT: &[u8] = b"esi:attempt";
pub const TAG_NAME_ESI_EXCEPT: &[u8] = b"esi:except";
pub const TAG_NAME_ESI_FOREACH: &[u8] = b"esi:foreach";
pub const TAG_NAME_ESI_BREAK: &[u8] = b"esi:break";
pub const TAG_NAME_SCRIPT: &[u8] = b"script";

// ============================================================================
// Expression Delimiters & Operators
// ============================================================================

// Quotes
pub const SINGLE_QUOTE: u8 = b'\'';
pub const DOUBLE_QUOTE: u8 = b'"';
pub const QUOTE_TRIPLE: &[u8] = b"'''";

// Brackets & Braces
pub const OPEN_PAREN: &[u8] = b"(";
pub const CLOSE_PAREN: &[u8] = b")";
pub const OPEN_BRACE: u8 = b'{';
pub const CLOSE_BRACE: u8 = b'}';
pub const OPEN_SQ_BRACKET: u8 = b'[';
pub const CLOSE_SQ_BRACKET: &[u8] = b"]";

// Punctuation
pub const COMMA: u8 = b',';
pub const COLON: u8 = b':';
pub const EQUALS: &[u8] = b"=";
pub const PIPE: &[u8] = b"|";

// Variable/function delimiters (multi-byte)
pub const VAR_OPEN: &[u8] = b"$(";

// Arithmetic Operators
pub const OP_ADD: &[u8] = b"+";
pub const OP_MULTIPLY: &[u8] = b"*";
pub const OP_DIVIDE: &[u8] = b"/";
pub const OP_MODULO: &[u8] = b"%";

// Comparison & Logical Operators (multi-byte)
pub const OP_EQUALS_COMP: &[u8] = b"==";
pub const OP_NOT_EQUALS: &[u8] = b"!=";
pub const OP_LESS_EQUAL: &[u8] = b"<=";
pub const OP_GREATER_EQUAL: &[u8] = b">=";
pub const OP_AND: &[u8] = b"&&";
pub const OP_OR: &[u8] = b"||";

// String Operators
pub const OP_MATCHES_I: &[u8] = b"matches_i";
pub const OP_MATCHES: &[u8] = b"matches";
pub const OP_HAS_I: &[u8] = b"has_i";
pub const OP_HAS: &[u8] = b"has";

// Range Operator
pub const OP_RANGE: &[u8] = b"..";

// ============================================================================
// Expression & Evaluation Constants
// ============================================================================

// Built-in Variable Names
pub const VAR_REQUEST_METHOD: &str = "REQUEST_METHOD";
pub const VAR_REQUEST_PATH: &str = "REQUEST_PATH";
pub const VAR_REMOTE_ADDR: &str = "REMOTE_ADDR";
pub const VAR_QUERY_STRING: &str = "QUERY_STRING";
pub const VAR_HTTP_PREFIX: &str = "HTTP_";
pub const VAR_MATCHES: &str = "MATCHES";

// Boolean Value Literals
pub const BOOL_TRUE: &[u8] = b"true";
pub const BOOL_FALSE: &[u8] = b"false";

// Function Names - String Operations
pub const FN_LOWER: &str = "lower";
pub const FN_UPPER: &str = "upper";
pub const FN_HTML_ENCODE: &str = "html_encode";
pub const FN_HTML_DECODE: &str = "html_decode";
pub const FN_CONVERT_TO_UNICODE: &str = "convert_to_unicode";
pub const FN_CONVERT_FROM_UNICODE: &str = "convert_from_unicode";
pub const FN_REPLACE: &str = "replace";
pub const FN_STR: &str = "str";
pub const FN_LSTRIP: &str = "lstrip";
pub const FN_RSTRIP: &str = "rstrip";
pub const FN_STRIP: &str = "strip";
pub const FN_SUBSTR: &str = "substr";

// Function Names - Encoding/Quoting
pub const FN_DOLLAR: &str = "dollar";
pub const FN_DQUOTE: &str = "dquote";
pub const FN_SQUOTE: &str = "squote";
pub const FN_BASE64_ENCODE: &str = "base64_encode";
pub const FN_BASE64_DECODE: &str = "base64_decode";
pub const FN_URL_ENCODE: &str = "url_encode";
pub const FN_URL_DECODE: &str = "url_decode";

// Function Names - Collection Operations
pub const FN_EXISTS: &str = "exists";
pub const FN_IS_EMPTY: &str = "is_empty";
pub const FN_STRING_SPLIT: &str = "string_split";
pub const FN_JOIN: &str = "join";
pub const FN_LIST_DELITEM: &str = "list_delitem";
pub const FN_LEN: &str = "len";
pub const FN_INDEX: &str = "index";
pub const FN_RINDEX: &str = "rindex";

// Function Names - Type Conversion
pub const FN_INT: &str = "int";

// Function Names - Cryptographic
pub const FN_DIGEST_MD5: &str = "digest_md5";
pub const FN_DIGEST_MD5_HEX: &str = "digest_md5_hex";
pub const FN_BIN_INT: &str = "bin_int";

// Function Names - Time Operations
pub const FN_TIME: &str = "time";
pub const FN_HTTP_TIME: &str = "http_time";
pub const FN_STRFTIME: &str = "strftime";

// Function Names - Random
pub const FN_RAND: &str = "rand";
pub const FN_LAST_RAND: &str = "last_rand";

// Function Names - HTTP Response
pub const FN_ADD_HEADER: &str = "add_header";
pub const FN_SET_RESPONSE_CODE: &str = "set_response_code";
pub const FN_SET_REDIRECT: &str = "set_redirect";

// Function Names - Test/Utility
pub const FN_PING: &str = "ping";
pub const FN_PONG: &str = "pong";

// Test URLs
pub const URL_LOCALHOST: &str = "http://localhost";
