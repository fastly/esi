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
//!     // Initialize processor with default configuration, passing in the
//!     // client request and backend response (ESI document).
//!     let processor = Processor::new(
//!         beresp.into_body(),
//!         Some(req),
//!         None,
//!         esi::Configuration::default();
//!     );
//!
//!     // Execute the processor, passing in callbacks for sending requests and processing responses.
//!     processor.execute(
//!         Some(&|req| {
//!             println!("Sending request {} {}", req.get_method(), req.get_path());
//!             Ok(req.with_ttl(120).send_async("origin_0")?)
//!         }),
//!         Some(&|req, resp| {
//!             println!(
//!                 "Received response for {} {}",
//!                 req.get_method(),
//!                 req.get_path()
//!             );
//!             Ok(resp)
//!         }),
//!     )?;
//!
//!     Ok(())
//! }
//! ```

mod config;
mod document;
mod error;
mod parse;

use fastly::http::body::StreamingBody;
use fastly::http::request::PendingRequest;
use fastly::http::{header, Method, StatusCode};
use fastly::{mime, Body, Request, Response};
use log::{debug, error};
use quick_xml::{Reader, Writer};
use std::collections::VecDeque;
use std::io::Write;

pub use crate::document::Element;
use crate::error::Result;
pub use crate::parse::{parse_tags, Event, Tag};

pub use crate::config::Configuration;
pub use crate::error::ExecutionError;

/// An instance of the ESI processor with a given configuration.
pub struct Processor {
    // The XML reader for the source document.
    xml_reader: Reader<Body>,
    // The original client request metadata, if any.
    original_request_metadata: Option<Request>,
    // The response headers to send to the client.
    client_response_metadata: Option<Response>,
    // The configuration for the processor.
    configuration: Configuration,
}

impl Processor {
    pub fn new(
        src_document: Body,
        original_request_metadata: Option<Request>,
        client_response_metadata: Option<Response>,
        configuration: Configuration,
    ) -> Self {
        // Create a parser for the ESI document
        let xml_reader = reader_from_body(src_document);

        debug!("processor initialized");

        Self {
            xml_reader,
            original_request_metadata,
            client_response_metadata,
            configuration,
        }
    }

    pub fn execute(
        mut self,
        dispatch_fragment_request: Option<&dyn Fn(Request) -> Result<PendingRequest>>,
        process_fragment_response: Option<&dyn Fn(Request, Response) -> Result<Response>>,
    ) -> Result<()> {
        let dispatch_fragment_request = dispatch_fragment_request.unwrap_or({
            // TODO: provide default
            &|_| panic!("no dispatch request function provided")
        });

        debug!("starting response stream");

        // Create a response to send the headers to the client
        let resp = self.client_response_metadata.unwrap_or_else(|| {
            Response::from_status(StatusCode::OK).with_content_type(mime::TEXT_HTML)
        });

        // Send the response headers to the client and open an output stream
        let output_stream = resp.stream_to_client();

        // Set up an XML writer to write directly to the client output stream.
        let mut xml_writer = Writer::new(output_stream);

        debug!("parsing document");

        // Set up the queue of document elements to be sent to the client.
        let mut elements: VecDeque<Element> = VecDeque::new();

        // If there is a source request to mimic, copy its metadata, otherwise use a default request.
        let original_request_metadata = if let Some(req) = &self.original_request_metadata {
            req.clone_without_body()
        } else {
            Request::new(Method::GET, "http://localhost")
        };

        // Begin parsing the source document
        parse_tags(
            &self.configuration.namespace.clone(),
            &mut self.xml_reader,
            &mut |event| {
                match event {
                    Event::ESI(Tag::Include {
                        src,
                        alt,
                        continue_on_error,
                    }) => {
                        debug!("got ESI");

                        // TODO: ALT AND CONTINUE ON ERROR
                        let req = build_fragment_request(
                            original_request_metadata.clone_without_body(),
                            &src,
                        );
                        let alt_req = alt.map(|alt| {
                            build_fragment_request(
                                original_request_metadata.clone_without_body(),
                                &alt,
                            )
                        });

                        let element = send_fragment_request(
                            req,
                            alt_req,
                            continue_on_error,
                            dispatch_fragment_request,
                        )?;
                        elements.push_back(element);
                    }
                    Event::XML(event) => {
                        debug!("got other content");
                        if elements.is_empty() {
                            debug!("nothing waiting so streaming directly to client");
                            xml_writer.write_event(event)?;
                            xml_writer.inner().flush().expect("failed to flush output");
                        } else {
                            debug!("pushing content to buffer, len: {}", elements.len());
                            let mut vec = Vec::new();
                            let mut writer = Writer::new(&mut vec);
                            writer.write_event(event)?;
                            elements.push_back(Element::Raw(vec));
                        }
                    }
                }

                poll_elements(
                    &mut elements,
                    &mut xml_writer,
                    dispatch_fragment_request,
                    process_fragment_response,
                )?;

                Ok(())
            },
        )?;

        // Wait for any pending requests to complete
        loop {
            if elements.is_empty() {
                break;
            }

            poll_elements(
                &mut elements,
                &mut xml_writer,
                dispatch_fragment_request,
                process_fragment_response,
            )?;
        }

        Ok(())
    }
}

fn build_fragment_request(mut request: Request, url: &str) -> Request {
    if url.starts_with('/') {
        request.get_url_mut().set_path(url);
    } else {
        request.set_url(url);
    }

    let hostname = request.get_url().host().expect("no host").to_string();

    request.set_header(header::HOST, &hostname);

    request
}

fn send_fragment_request(
    req: Request,
    alt: Option<Request>,
    continue_on_error: bool,
    dispatch_request: &dyn Fn(Request) -> Result<PendingRequest>,
) -> Result<Element> {
    debug!("Requesting ESI fragment: {}", req.get_url());

    let req_metadata = req.clone_without_body();

    let pending_request = match dispatch_request(req) {
        Ok(req) => req,
        Err(err) => {
            error!("Failed to dispatch request: {:?}", err);
            return Err(err);
        }
    };

    Ok(Element::Fragment(
        req_metadata,
        alt,
        continue_on_error,
        pending_request,
    ))
}

// This function is responsible for polling pending requests and writing their
// responses to the client output stream. It also handles any queued source
// content that needs to be written to the client output stream.
fn poll_elements(
    elements: &mut VecDeque<Element>,
    xml_writer: &mut Writer<StreamingBody>,
    dispatch_request: &dyn Fn(Request) -> Result<PendingRequest>,
    process_response: Option<&dyn Fn(Request, Response) -> Result<Response>>,
) -> Result<()> {
    loop {
        let element = elements.pop_front();

        if let Some(element) = element {
            match element {
                Element::Raw(raw) => {
                    debug!("writing previously queued other content");
                    xml_writer.inner().write_all(&raw).unwrap();
                }
                Element::Fragment(request, alt, continue_on_error, pending_request) => {
                    match pending_request.poll() {
                        fastly::http::request::PollResult::Pending(pending_request) => {
                            elements.insert(
                                0,
                                Element::Fragment(request, alt, continue_on_error, pending_request),
                            );
                            break;
                        }
                        fastly::http::request::PollResult::Done(Ok(res)) => {
                            if !res.get_status().is_success() {
                                if let Some(alt) = alt {
                                    debug!("request poll DONE ERROR, trying alt");
                                    let pending_request = dispatch_request(alt)?;
                                    elements.insert(
                                        0,
                                        Element::Fragment(
                                            request,
                                            None,
                                            continue_on_error,
                                            pending_request,
                                        ),
                                    );
                                    break;
                                } else if continue_on_error {
                                    debug!("request poll DONE ERROR, NO ALT, continuing");
                                    continue;
                                } else {
                                    debug!("request poll DONE ERROR, NO ALT, failing");
                                    todo!("request failed non-continuable");
                                }
                            } else {
                                let res = if let Some(process_response) = process_response {
                                    process_response(request, res)?
                                } else {
                                    res
                                };

                                xml_writer
                                    .inner()
                                    .write_all(&res.into_body_bytes())
                                    .unwrap();
                                xml_writer.inner().flush().expect("failed to flush output");
                            }
                        }
                        fastly::http::request::PollResult::Done(Err(_err)) => {
                            todo!()
                        }
                    }
                }
            }
        } else {
            break;
        }
    }

    Ok(())
}

// Helper function to create an XML reader from a body.
fn reader_from_body(body: Body) -> Reader<Body> {
    let mut reader = Reader::from_reader(body);

    // TODO: make this configurable
    reader.check_end_names(false);

    reader
}
