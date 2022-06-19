//! # ESI for Fastly
//!
//! This crate provides a streaming Edge Side Includes parser and executor designed for Fastly Compute@Edge.
//!
//! The implementation is currently a subset of the [ESI Language Specification 1.0](https://www.w3.org/TR/esi-lang/), so
//! only the `esi:include` tag is supported. Other tags will be ignored.
//!
//! ## Usage Example
//!
//! ```rust,no_run
//! use esi::Processor;
//! use fastly::{http::StatusCode, mime, Error, Request, Response};
//!
//! fn main() {
//!     if let Err(err) = handle_request(Request::from_client()) {
//!         println!("returning error response");
//!
//!         Response::from_status(StatusCode::INTERNAL_SERVER_ERROR)
//!             .with_body(err.to_string())
//!             .send_to_client();
//!     }
//! }
//!
//! fn handle_request(req: Request) -> Result<(), Error> {
//!     // Fetch ESI document from backend.
//!     let beresp = req.clone_without_body().send("origin_0")?;
//!
//!     // Construct an ESI processor with the default configuration.
//!     let config = esi::Configuration::default();
//!     let processor = Processor::new(config);
//!
//!     // Execute the ESI document using the client request as context
//!     // and sending all requests to the backend `origin_1`.
//!     processor.execute_esi(req, beresp, &|req| {
//!         Ok(req.with_ttl(120).send("origin_1")?)
//!     })?;
//!
//!     Ok(())
//! }
//! ```

mod config;
mod error;
mod parse;

use fastly::http::body::StreamingBody;
use fastly::http::header;
use fastly::{Body, Request, Response};
use log::{debug, error, warn};
use quick_xml::{Reader, Writer};
use std::io::Write;

use crate::error::Result;
pub use crate::parse::{parse_tags, Event, Tag};

pub use crate::config::Configuration;
pub use crate::error::ExecutionError;

/// An instance of the ESI processor with a given configuration.
#[derive(Default)]
pub struct Processor<'a> {
    configuration: Configuration<'a>,
}

impl<'a> Processor<'a> {
    /// Construct a new ESI processor with the given configuration.
    pub fn new(configuration: Configuration<'a>) -> Self {
        Self { configuration }
    }
}

impl<'a> Processor<'a> {
    /// Execute the ESI document (`document`) using the provided client request (`original_request`) as context,
    /// and stream the resulting output to the client.
    ///
    /// The `request_handler` parameter is a closure that is called for each ESI fragment request.
    pub fn execute_esi(
        &self,
        original_request: Request,
        mut document: Response,
        request_handler: &dyn Fn(Request) -> Result<Response>,
    ) -> Result<()> {
        // Create a parser for the ESI document
        let body = document.take_body();
        let xml_reader = reader_from_body(body);

        // Send the response headers to the client and open an output stream
        let output = document.stream_to_client();

        // Set up an XML writer to write directly to the client output stream.
        let mut xml_writer = Writer::new(output);

        // Parse the ESI document and stream it to the XML writer.
        match self.execute_esi_fragment(
            original_request,
            xml_reader,
            &mut xml_writer,
            request_handler,
        ) {
            Ok(_) => Ok(()),
            Err(err) => {
                error!("error executing ESI: {:?}", err);
                xml_writer.write(b"\nAn error occurred while constructing this document.\n")?;
                xml_writer
                    .inner()
                    .flush()
                    .expect("failed to flush error message");
                Err(err)
            }
        }
    }

    /// Execute the ESI fragment (`fragment`) using the provided client request (`original_request`) as context.
    ///
    /// Rather than sending the result of the execution to the client, this function will write XML tags directly
    /// to the given `xml_writer`, allowing for nesting.
    pub fn execute_esi_fragment(
        &self,
        original_request: Request,
        mut xml_reader: Reader<Body>,
        xml_writer: &mut Writer<StreamingBody>,
        request_handler: &dyn Fn(Request) -> Result<Response>,
    ) -> Result<()> {
        // Parse the ESI fragment
        parse_tags(
            &self.configuration.namespace,
            &mut xml_reader,
            &mut |event| {
                match event {
                    Event::ESI(Tag::Include {
                        src,
                        alt,
                        continue_on_error,
                    }) if (self.configuration.is_match)(&src) => {
                        let resp = match self.send_esi_fragment_request(
                            &original_request,
                            &src,
                            request_handler,
                        ) {
                            Ok(resp) => Some(resp),
                            Err(err) => {
                                warn!("Request to {} failed: {:?}", src, err);
                                if let Some(alt) = alt {
                                    warn!("Trying `alt` instead: {}", alt);
                                    match self.send_esi_fragment_request(
                                        &original_request,
                                        &alt,
                                        request_handler,
                                    ) {
                                        Ok(resp) => Some(resp),
                                        Err(err) => {
                                            debug!("Alt request to {} failed: {:?}", alt, err);
                                            if continue_on_error {
                                                None
                                            } else {
                                                return Err(err);
                                            }
                                        }
                                    }
                                } else {
                                    error!("Fragment request failed with no `alt` available");
                                    if continue_on_error {
                                        None
                                    } else {
                                        return Err(err);
                                    }
                                }
                            }
                        };

                        if let Some(mut resp) = resp {
                            if self.configuration.recursive {
                                let fragment_xml_reader = reader_from_body(resp.take_body());
                                self.execute_esi_fragment(
                                    original_request.clone_without_body(),
                                    fragment_xml_reader,
                                    xml_writer,
                                    request_handler,
                                )?;
                            } else if let Err(err) =
                                xml_writer.inner().write_all(&resp.take_body().into_bytes())
                            {
                                error!("Failed to write fragment body: {}", err);
                            }
                        } else {
                            error!("No content for fragment");
                        }
                    }
                    Event::ESI(Tag::Include {
                        src,
                        alt,
                        continue_on_error,
                    }) => {
                        let continue_str = if continue_on_error {
                            "onerror=\"continue\""
                        } else {
                            ""
                        };
                        let alt_str = match alt {
                            Some(alt) => format!("alt=\"{}\"", alt),
                            None => "".to_string(),
                        };
                        let message = format!(
                            r#"<esi:include src="{}" {} {}></esi:include>"#,
                            src, alt_str, continue_str
                        );
                        xml_writer.write(message.as_bytes())?;
                        xml_writer.inner().flush().expect("failed to flush output");
                    }
                    Event::XML(event) => {
                        xml_writer.write_event(event)?;
                        xml_writer.inner().flush().expect("failed to flush output");
                    }
                }
                Ok(())
            },
        )?;

        Ok(())
    }

    fn send_esi_fragment_request(
        &self,
        original_request: &Request,
        url: &str,
        request_handler: &dyn Fn(Request) -> Result<Response>,
    ) -> Result<Response> {
        let mut req = original_request.clone_without_body();

        if url.starts_with('/') {
            req.get_url_mut().set_path(url);
        } else {
            req.set_url(url);
        }

        let hostname = req.get_url().host().expect("no host").to_string();

        req.set_header(header::HOST, &hostname);

        debug!("Requesting ESI fragment: {}", url);

        let resp = request_handler(req)?;
        if resp.get_status().is_success() {
            Ok(resp)
        } else {
            Err(ExecutionError::UnexpectedStatus(resp.get_status().as_u16()))
        }
    }
}

fn reader_from_body(body: Body) -> Reader<Body> {
    let mut reader = Reader::from_reader(body);

    // TODO: make this configurable
    reader.check_end_names(false);

    reader
}
