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
//!     let mut beresp = req.clone_without_body().send("origin_0")?;
//!
//!     // If the response is HTML, we can parse it for ESI tags.
//!     if beresp
//!         .get_content_type()
//!         .map(|c| c.subtype() == mime::HTML)
//!         .unwrap_or(false)
//!     {
//!         let processor = esi::Processor::new(
//!             // The original client request.
//!             Some(req),
//!             // Use the default ESI configuration.
//!             esi::Configuration::default()
//!         );
//!
//!         processor.process_response(
//!             // The ESI source document. Note that the body will be consumed.
//!             &mut beresp,
//!             // Optionally provide a template for the client response.
//!             Some(Response::from_status(StatusCode::OK).with_content_type(mime::TEXT_HTML)),
//!             // Provide logic for sending fragment requests, otherwise the hostname
//!             // of the request URL will be used as the backend name.
//!             Some(&|req| {
//!                 println!("Sending request {} {}", req.get_method(), req.get_path());
//!                 Ok(Some(req.with_ttl(120).send_async("mock-s3")?))
//!             }),
//!             // Optionally provide a method to process fragment responses before they
//!             // are streamed to the client.
//!             Some(&|req, resp| {
//!                 println!(
//!                     "Received response for {} {}",
//!                     req.get_method(),
//!                     req.get_path()
//!                 );
//!                 Ok(resp)
//!             }),
//!         )?;
//!     } else {
//!         // Otherwise, we can just return the response.
//!         beresp.send_to_client();
//!     }
//!
//!     Ok(())
//! }
//! ```

mod config;
mod document;
mod error;
mod parse;

use fastly::http::request::PendingRequest;
use fastly::http::{header, Method, StatusCode, Url};
use fastly::{mime, Body, Request, Response};
use log::{debug, error};
use quick_xml::{Reader, Writer};
use std::collections::VecDeque;
use std::io::{BufRead, Write};

pub use crate::document::Element;
use crate::error::Result;
pub use crate::parse::{parse_tags, Event, Tag};

pub use crate::config::Configuration;
pub use crate::error::ExecutionError;

/// An instance of the ESI processor with a given configuration.
pub struct Processor {
    // The original client request metadata, if any.
    original_request_metadata: Option<Request>,
    // The configuration for the processor.
    configuration: Configuration,
}

impl Processor {
    pub fn new(original_request_metadata: Option<Request>, configuration: Configuration) -> Self {
        Self {
            original_request_metadata,
            configuration,
        }
    }

    /// Process a response body as an ESI document. Consumes the response body.
    pub fn process_response(
        self,
        src_document: &mut Response,
        client_response_metadata: Option<Response>,
        dispatch_fragment_request: Option<&dyn Fn(Request) -> Result<Option<PendingRequest>>>,
        process_fragment_response: Option<&dyn Fn(Request, Response) -> Result<Response>>,
    ) -> Result<()> {
        // Create a response to send the headers to the client
        let resp = client_response_metadata.unwrap_or_else(|| {
            Response::from_status(StatusCode::OK).with_content_type(mime::TEXT_HTML)
        });

        // Send the response headers to the client and open an output stream
        let output_writer = resp.stream_to_client();

        // Set up an XML writer to write directly to the client output stream.
        let mut xml_writer = Writer::new(output_writer);

        match self.process_document(
            reader_from_body(src_document.take_body()),
            &mut xml_writer,
            dispatch_fragment_request,
            process_fragment_response,
        ) {
            Ok(()) => {
                xml_writer.into_inner().finish().unwrap();
                Ok(())
            }
            Err(err) => {
                error!("error processing ESI document: {}", err);
                Err(err)
            }
        }
    }

    /// Process an ESI document from a [`quick_xml::Reader`].
    pub fn process_document(
        self,
        mut src_document: Reader<impl BufRead>,
        output_writer: &mut Writer<impl Write>,
        dispatch_fragment_request: Option<&dyn Fn(Request) -> Result<Option<PendingRequest>>>,
        process_fragment_response: Option<&dyn Fn(Request, Response) -> Result<Response>>,
    ) -> Result<()> {
        let dispatch_fragment_request = dispatch_fragment_request.unwrap_or({
            &|req| {
                debug!("no dispatch method configured, defaulting to hostname");
                let backend = req
                    .get_url()
                    .host()
                    .unwrap_or_else(|| panic!("no host in request: {}", req.get_url()))
                    .to_string();
                let pending_req = req.send_async(backend)?;
                Ok(Some(pending_req))
            }
        });

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
            &self.configuration.namespace,
            &mut src_document,
            &mut |event| {
                debug!("got {:?}", event);
                match event {
                    Event::ESI(Tag::Include {
                        src,
                        alt,
                        continue_on_error,
                    }) => {
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

                        if let Some(element) = send_fragment_request(
                            req?,
                            alt_req,
                            continue_on_error,
                            dispatch_fragment_request,
                        )? {
                            elements.push_back(element);
                        }
                    }
                    Event::XML(event) => {
                        if elements.is_empty() {
                            debug!("nothing waiting so streaming directly to client");
                            output_writer.write_event(event)?;
                            output_writer
                                .inner()
                                .flush()
                                .expect("failed to flush output");
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
                    output_writer,
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
                output_writer,
                dispatch_fragment_request,
                process_fragment_response,
            )?;
        }

        Ok(())
    }
}

fn build_fragment_request(mut request: Request, url: &str) -> Result<Request> {
    let escaped_url = match quick_xml::escape::unescape(url) {
        Ok(url) => url,
        Err(err) => {
            return Err(ExecutionError::InvalidRequestUrl(err.to_string()));
        }
    }
    .to_string();

    if escaped_url.starts_with('/') {
        match Url::parse(
            format!("{}://0.0.0.0{}", request.get_url().scheme(), escaped_url).as_str(),
        ) {
            Ok(u) => {
                request.get_url_mut().set_path(u.path());
                request.get_url_mut().set_query(u.query());
            }
            Err(_err) => {
                return Err(ExecutionError::InvalidRequestUrl(escaped_url));
            }
        };
    } else {
        request.set_url(match Url::parse(&escaped_url) {
            Ok(url) => url,
            Err(_err) => {
                return Err(ExecutionError::InvalidRequestUrl(escaped_url));
            }
        });
    }

    let hostname = request.get_url().host().expect("no host").to_string();

    request.set_header(header::HOST, &hostname);

    Ok(request)
}

fn send_fragment_request(
    req: Request,
    alt: Option<Result<Request>>,
    continue_on_error: bool,
    dispatch_request: &dyn Fn(Request) -> Result<Option<PendingRequest>>,
) -> Result<Option<Element>> {
    debug!("Requesting ESI fragment: {}", req.get_url());

    let req_metadata = req.clone_without_body();

    let pending_request = match dispatch_request(req) {
        Ok(Some(req)) => req,
        Ok(None) => {
            debug!("No pending request returned, skipping");
            return Ok(None);
        }
        Err(err) => {
            error!("Failed to dispatch request: {:?}", err);
            return Err(err);
        }
    };

    Ok(Some(Element::Fragment(
        req_metadata,
        alt,
        continue_on_error,
        pending_request,
    )))
}

// This function is responsible for polling pending requests and writing their
// responses to the client output stream. It also handles any queued source
// content that needs to be written to the client output stream.
fn poll_elements(
    elements: &mut VecDeque<Element>,
    output_writer: &mut Writer<impl Write>,
    dispatch_fragment_request: &dyn Fn(Request) -> Result<Option<PendingRequest>>,
    process_fragment_response: Option<&dyn Fn(Request, Response) -> Result<Response>>,
) -> Result<()> {
    loop {
        let element = elements.pop_front();

        if let Some(element) = element {
            match element {
                Element::Raw(raw) => {
                    debug!("writing previously queued other content");
                    output_writer.inner().write_all(&raw).unwrap();
                }
                Element::Fragment(request, alt, continue_on_error, pending_request) => {
                    match pending_request.poll() {
                        fastly::http::request::PollResult::Pending(pending_request) => {
                            // Request is still pending, re-add it to the front of the queue and wait for the next poll.
                            elements.insert(
                                0,
                                Element::Fragment(request, alt, continue_on_error, pending_request),
                            );
                            break;
                        }
                        fastly::http::request::PollResult::Done(Ok(res)) => {
                            // Request has completed, check the status code and either continue, fallback to an alt, or fail.
                            if !res.get_status().is_success() {
                                if let Some(alt) = alt {
                                    debug!("request poll DONE ERROR, trying alt");
                                    if let Some(pending_request) = dispatch_fragment_request(alt?)?
                                    {
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
                                    } else {
                                        debug!("guest returned None, continuing");
                                        continue;
                                    }
                                } else if continue_on_error {
                                    debug!("request poll DONE ERROR, NO ALT, continuing");
                                    continue;
                                } else {
                                    debug!("request poll DONE ERROR, NO ALT, failing");
                                    return Err(ExecutionError::UnexpectedStatus(
                                        request.get_url_str().to_string(),
                                        res.get_status().into(),
                                    ));
                                }
                            } else {
                                // Response status is success, let the guest app process it if needed.
                                let res = if let Some(process_response) = process_fragment_response
                                {
                                    process_response(request, res)?
                                } else {
                                    res
                                };

                                // Write the response body to the output stream.
                                output_writer
                                    .inner()
                                    .write_all(&res.into_body_bytes())
                                    .unwrap();
                                output_writer
                                    .inner()
                                    .flush()
                                    .expect("failed to flush output");
                            }
                        }
                        fastly::http::request::PollResult::Done(Err(err)) => {
                            return Err(ExecutionError::RequestError(err))
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
