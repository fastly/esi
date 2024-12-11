use std::{collections::HashMap, io::Write};

use esi::{parse_tags, Reader, Writer};
use fastly::{http::StatusCode, mime, Request, Response};
use log::{error, info};

// Take a list of fragment URLs and return a map that maps each URL to a variant for the specific request.
fn get_variant_urls(urls: Vec<String>) -> HashMap<String, String> {
    let mut variant_urls = HashMap::new();
    for url in urls {
        // For demonstration, add a query parameter to each request
        let variant_url = if url.contains('?') {
            format!("{}&variant=1", url)
        } else {
            format!("{}?variant=1", url)
        };
        variant_urls.insert(url, variant_url);
    }
    variant_urls
}

fn main() {
    env_logger::builder()
        .filter(None, log::LevelFilter::Trace)
        .init();

    let req = Request::from_client();

    if req.get_path() != "/" {
        Response::from_status(StatusCode::NOT_FOUND).send_to_client();
        return;
    }

    // Generate synthetic test response from "index.html" file.
    // You probably want replace this with a backend call, e.g. `req.clone_without_body().send("origin_0")`
    let mut beresp =
        Response::from_body(include_str!("index.html")).with_content_type(mime::TEXT_HTML);

    // If the response is HTML, we can parse it for ESI tags.
    if beresp
        .get_content_type()
        .is_some_and(|c| c.subtype() == mime::HTML)
    {
        let processor = esi::Processor::new(Some(req), esi::Configuration::default());

        // Create a response to send the headers to the client
        let resp = Response::from_status(StatusCode::OK).with_content_type(mime::TEXT_HTML);

        // Send the response headers to the client and open an output stream
        let output_writer = resp.stream_to_client();

        // Set up an XML writer to write directly to the client output stream.
        let mut xml_writer = Writer::new(output_writer);

        // Parse the ESI document and store it in memory
        let mut events = Vec::new();
        let mut beresp_reader = Reader::from_reader(beresp.take_body());
        parse_tags("esi", &mut beresp_reader, &mut |event| {
            events.push(event);
            Ok(())
        })
        .expect("failed to parse ESI template");

        // Extract the `src` URLs from ESI includes
        let urls = events
            .iter()
            .filter_map(|event| match event {
                esi::Event::ESI(esi::Tag::Include { src, .. }) => Some(src.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();

        // Check the variant database to determine the URLs to fetch
        let variant_urls = get_variant_urls(urls);

        // Process the already-parsed ESI document, replacing the request URLs with the variant URLs
        let result = processor.process_parsed_document(
            events.into(),
            &mut xml_writer,
            Some(&move |req| {
                let original_url = req.get_url().to_string();
                let variant_url = variant_urls.get(&original_url).unwrap_or(&original_url);
                info!(
                    "Sending request - original URL: ({}) variant URL: ({})",
                    req.get_path(),
                    variant_url
                );
                Ok(esi::PendingFragmentContent::PendingRequest(
                    req.with_url(variant_url)
                        .with_ttl(120)
                        .send_async("mock-s3")?,
                ))
            }),
            Some(&|req, resp| {
                info!(
                    "Received response for {} {}",
                    req.get_method(),
                    req.get_path()
                );
                Ok(resp)
            }),
        );

        match result {
            Ok(()) => {
                xml_writer.into_inner().finish().unwrap();
            }
            Err(err) => {
                error!("error processing ESI document: {}", err);
                let _ = xml_writer.get_mut().write(b"Internal server error");
                xml_writer.into_inner().finish().unwrap_or_else(|_| {
                    error!("error flushing error response to client");
                });
            }
        }
    } else {
        // Otherwise, we can just return the response.
        beresp.send_to_client();
    }
}
