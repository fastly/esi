use thiserror::Error;

use fastly::http::request::SendError;

/// Describes an error encountered during ESI parsing or execution.
#[derive(Error, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum ExecutionError {
    /// Invalid XML was encountered during parsing.
    #[error("xml parsing error: {0}")]
    XMLError(#[from] quick_xml::Error),

    /// The ESI document contains a tag with a missing paraemter.
    #[error("tag `{0}` is missing required parameter `{1}`")]
    MissingRequiredParameter(String, String),

    /// The ESI document contains an opening tag where it doesn't belong.
    #[error("unexpected `{0}` opening tag")]
    UnexpectedOpeningTag(String),

    /// The ESI document contains an opening tag without a matching closing tag.
    #[error("unexpected `{0}` closing tag")]
    UnexpectedClosingTag(String),

    // One or more of the URLs in the ESI template were invalid.
    #[error("invalid request URL provided: `{0}`")]
    InvalidRequestUrl(String),

    /// An error occurred when sending a fragment request to a backend.
    #[error("error sending request: {0}")]
    RequestError(#[from] SendError),

    /// An ESI fragment request returned an unexpected HTTP status code.
    #[error("received unexpected status code for fragment `{0}`: {1}")]
    UnexpectedStatus(String, u16),

    /// This error is returned when the parser encounters an unexpected end of document.
    #[error("unexpected end of document")]
    UnexpectedEndOfDocument,

    /// Writer error
    #[error("writer error: {0}")]
    WriterError(#[from] std::io::Error),

    /// Expression parse error
    #[error("expression failed to parse: `{0}`")]
    ExpressionParseError(String),
}

pub type Result<T> = std::result::Result<T, ExecutionError>;
