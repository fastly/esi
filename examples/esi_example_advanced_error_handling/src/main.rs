use std::io::Write;

use fastly::{http::StatusCode, mime, Request, Response};
use log::{error, info};

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
        let mut output_writer = resp.stream_to_client();

        // Process the ESI document
        let reader = std::io::BufReader::new(beresp.take_body());
        let result = processor.process_document(
            reader,
            &mut output_writer,
            Some(&|req| {
                info!("Sending request {} {}", req.get_method(), req.get_path());
                Ok(req.with_ttl(120).send_async("mock-s3")?.into())
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
                output_writer.finish().unwrap();
            }
            Err(err) => {
                error!("error processing ESI document: {err}");
                let _ = output_writer.write(include_bytes!("error.html.fragment"));
                output_writer.finish().unwrap_or_else(|_| {
                    error!("error flushing error response to client");
                });
            }
        }
    } else {
        // Otherwise, we can just return the response.
        beresp.send_to_client();
    }
}
