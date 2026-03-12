use thiserror::Error;

use fastly::http::request::SendError;

/// Describes an error encountered during ESI document processing.
///
/// This is the main error type for the ESI crate, covering parsing failures,
/// fragment request errors, expression evaluation errors, and I/O errors.
#[derive(Error, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum ESIError {
    // One or more of the URLs in the ESI template were invalid.
    #[error("invalid request URL provided: `{0}`")]
    InvalidRequestUrl(String),

    /// An error occurred when sending a fragment request to a backend.
    #[error("error sending request: {0}")]
    RequestError(#[from] SendError),

    /// An ESI fragment request returned an unexpected HTTP status code.
    #[error("received unexpected status code for fragment `{url}`: {status}")]
    UnexpectedStatus { url: String, status: u16 },

    /// This error is returned when the parser encounters an unexpected end of document.
    #[error("unexpected end of document")]
    UnexpectedEndOfDocument,

    /// Writer error
    #[error("writer error: {0}")]
    WriterError(#[from] std::io::Error),

    /// An error occurred while creating a regular expression in an eval context.
    #[error("failed to create a regular expression")]
    RegexError(#[from] regex::Error),

    /// An error occurred while executing a function in an eval context.
    #[error("failed to execute a function: `{0}`")]
    FunctionError(String),

    /// An error occurred during variable assignment (e.g., out of bounds, type mismatch).
    #[error("variable assignment error: `{0}`")]
    VariableError(String),

    /// Fragment fetch lifecycle error (dispatch, wait, HTTP status, backend creation).
    #[error("fragment request error: {0}")]
    FragmentRequestError(String),

    /// ESI sub-document parse failure (eval fragments, dca=esi fragments).
    #[error("parse error: {0}")]
    ParseError(String),

    /// ESI expression evaluation failure (operators, type mismatches, etc.).
    #[error("expression evaluation error: {0}")]
    ExpressionError(String),

    /// Streaming processor detected an infinite loop.
    #[error("infinite loop detected after {iterations} iterations (buffer len: {buffer_len}, eof: {eof})")]
    InfiniteLoop {
        iterations: usize,
        buffer_len: usize,
        eof: bool,
    },

    /// Invalid fragment request configuration (bad method, invalid UTF-8, etc.).
    #[error("invalid fragment configuration: {0}")]
    InvalidFragmentConfig(String),

    /// Internal consistency error (missing correlation slot, pending slot after drain, etc.).
    #[error("internal error: {0}")]
    InternalError(String),
}

pub type Result<T> = std::result::Result<T, ESIError>;
