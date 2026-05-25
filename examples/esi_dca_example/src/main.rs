use fastly::{http::StatusCode, mime, Error, Request, Response};
use log::info;

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
    let mut beresp =
        Response::from_body(include_str!("index.html")).with_content_type(mime::TEXT_HTML);

    // If the response is HTML, we can parse it for ESI tags.
    if beresp
        .get_content_type()
        .is_some_and(|c| c.subtype() == mime::HTML)
    {
        // Configure DCA (Dynamic Content Assembly) options:
        //  - default_dca = Esi: fragments without an explicit `dca` attribute
        //    are ESI-processed (Akamai-style behaviour).
        //  - enable_edge_control: honour `Edge-Control: dca=esi` response
        //    headers from fragment backends.
        //  - inherit_parent_dca: children inside a `dca="esi"` subtree
        //    inherit ESI processing without needing their own attribute.
        //  - max_include_depth = 5: limit nesting to 5 levels.
        let config = esi::Configuration::default()
            .with_default_dca(esi::DcaMode::Esi)
            .with_edge_control(true)
            .with_inherit_parent_dca(true)
            .with_max_include_depth(5);

        let processor = esi::Processor::new(Some(req), config);

        processor.process_response(
            &mut beresp,
            None,
            Some(&|req, _maxwait: Option<u32>| {
                info!("Sending request {} {}", req.get_method(), req.get_path());
                Ok(req.with_ttl(120).send_async("mock-s3")?.into())
            }),
            Some(&|req, mut resp| {
                info!(
                    "Received response for {} {}",
                    req.get_method(),
                    req.get_path()
                );
                if !resp.get_status().is_success() {
                    resp.set_status(StatusCode::OK);
                }
                Ok(resp)
            }),
        )?;
    } else {
        // Otherwise, we can just return the response.
        beresp.send_to_client();
    }

    Ok(())
}
