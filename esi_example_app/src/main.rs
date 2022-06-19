use esi::Processor;
use fastly::{http::StatusCode, mime, Error, Request, Response};

fn main() {
    env_logger::builder()
        .filter(None, log::LevelFilter::Trace)
        .init();

    if let Err(err) = handle_request(Request::from_client()) {
        println!("returning error response");

        Response::from_status(StatusCode::INTERNAL_SERVER_ERROR)
            .with_body(err.to_string())
            .send_to_client();
    }
}

fn handle_request(req: Request) -> Result<(), Error> {
    if req.get_path() != "/" {
        Response::from_status(StatusCode::NOT_FOUND).send_to_client();
        return Ok(());
    }

    // Generate synthetic test response from "index.html" file.
    // You probably want replace this with a backend call, e.g. `req.clone_without_body().send("origin_0")`
    let beresp = Response::from_body(include_str!("index.html")).with_content_type(mime::TEXT_HTML);

    // If the response is HTML, we can parse it for ESI tags.
    if beresp
        .get_content_type()
        .map(|c| c.subtype() == mime::HTML)
        .unwrap_or(false)
    {
        let config = esi::Configuration::default()
            .with_recursion()
            .with_matcher(&|src| !src.contains("ignore"));

        let processor = Processor::new(config);

        processor.execute_esi(req, beresp, &|req| Ok(req.with_ttl(120).send("mock-s3")?))?;

        Ok(())
    } else {
        // Otherwise, we can just return the response.
        beresp.send_to_client();
        Ok(())
    }
}
