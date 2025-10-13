use std::collections::VecDeque;

use crate::{PendingFragmentContent, Result};
use fastly::Request;
use quick_xml::Writer;

/// Represents a fragment of a document that can be fetched and processed.
///
/// A `Fragment` contains the necessary information to make a request for a part of a document,
/// handle potential errors, and retrieve the content asynchronously.
///
/// # Fields
///
/// * `request` - Metadata of the request.
/// * `alt` - An optional alternate request to send if the original request fails.
/// * `continue_on_error` - Whether to continue processing on error.
/// * `pending_content` - The pending fragment response, which can be polled to retrieve the content.
pub struct Fragment {
    // Metadata of the request
    pub(crate) request: Request,
    // An optional alternate request to send if the original request fails
    pub(crate) alt: Option<Result<Request>>,
    // Whether to continue on error
    pub(crate) continue_on_error: bool,
    // The pending fragment response, which can be polled to retrieve the content
    pub(crate) pending_content: PendingFragmentContent,
}

/// `Task` is combining raw data and an include fragment for both `attempt` and `except` arms
/// the result is written to `output`.
///
/// # Fields:
///
/// * `queue` - A queue of elements to process.
/// * `output` - The writer to write the processed data to.
/// * `status` - The status of the fetch operation.
pub struct Task {
    pub queue: VecDeque<Element>,
    pub output: Writer<Vec<u8>>,
    pub status: FetchState,
}

impl Default for Task {
    fn default() -> Self {
        Self {
            queue: VecDeque::new(),
            output: Writer::new(Vec::new()),
            status: FetchState::default(),
        }
    }
}

impl Task {
    pub fn new() -> Self {
        Self::default()
    }
}

/// A section of the pending response, either raw XML data or a pending fragment request.
/// * `Raw` - Raw XML data.
/// * `Include` - A pending fragment request.
/// * `Try` - A try block with an attempt and except task.
///
pub enum Element {
    Raw(Vec<u8>),
    Include(Box<Fragment>),
    Try {
        except_task: Box<Task>,
        attempt_task: Box<Task>,
    },
}

/// The state of a fetch operation.
/// * `Failed` - The request failed with the given status code.
/// * `Pending` - The request is still pending.
/// * `Succeeded` - The request succeeded.
///
pub enum FetchState {
    Failed(Request, u16),
    Pending,
    Succeeded,
}
impl Clone for FetchState {
    fn clone(&self) -> Self {
        match self {
            Self::Failed(req, res) => Self::Failed(req.clone_without_body(), *res),
            Self::Pending => Self::Pending,
            Self::Succeeded => Self::Succeeded,
        }
    }
}
impl Default for FetchState {
    fn default() -> Self {
        Self::Pending
    }
}

impl std::fmt::Debug for Element {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Raw(_) => write!(f, "Raw"),
            Self::Include(fragment) if fragment.alt.is_some() => {
                write!(f, "Include Fragment(with alt)")
            }
            Self::Include(_) => write!(f, "Include Fragment"),
            Self::Try {
                attempt_task,
                except_task,
            } => write!(
                f,
                "Try - Attempt: {:?}, Except: {:?}",
                attempt_task.queue, except_task.queue
            ),
        }
    }
}
