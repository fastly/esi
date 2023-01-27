# esi

//TODO BEFORE RELEASE
- error handling


A streaming Edge Side Includes parser and executor designed for Fastly Compute@Edge.

The implementation is currently a subset of the [ESI Language Specification 1.0](https://www.w3.org/TR/esi-lang/), supporting the following tags:

- `<esi:include>` (+ `alt`, `onerror="continue"`)
- `<esi:comment>`
- `<esi:remove>`

Other tags will be ignored.

## Example Usage

```rust,no_run
use fastly::{http::StatusCode, mime, Error, Request, Response};

fn main() {
    if let Err(err) = handle_request(Request::from_client()) {
        println!("returning error response");

        Response::from_status(StatusCode::INTERNAL_SERVER_ERROR)
            .with_body(err.to_string())
            .send_to_client();
    }
}

fn handle_request(req: Request) -> Result<(), Error> {
    // Fetch ESI document from backend.
    let mut beresp = req.clone_without_body().send("origin_0")?;

    // If the response is HTML, we can parse it for ESI tags.
    if beresp
        .get_content_type()
        .map(|c| c.subtype() == mime::HTML)
        .unwrap_or(false)
    {
        let processor = esi::Processor::new(
            // The original client request.
            Some(req),
            // Optionally provide a template for the client response.
            Some(Response::from_status(StatusCode::OK).with_content_type(mime::TEXT_HTML)),
            // Use the default ESI configuration.
            esi::Configuration::default()
        );

        processor.execute(
            // The ESI source document. Note that the body will be consumed.
            &mut beresp,
            // Provide logic for sending fragment requests, otherwise the hostname
            // of the request URL will be used as the backend name.
            Some(&|req| {
                println!("Sending request {} {}", req.get_method(), req.get_path());
                Ok(Some(req.with_ttl(120).send_async("mock-s3")?))
            }),
            // Optionally provide a method to process fragment responses before they
            // are streamed to the client.
            Some(&|req, resp| {
                println!(
                    "Received response for {} {}",
                    req.get_method(),
                    req.get_path()
                );
                Ok(resp)
            }),
        )?;

        Ok(())
    } else {
        // Otherwise, we can just return the response.
        beresp.send_to_client();
        Ok(())
    }
}
```

See a full example app in the [`esi_example_app`](./esi_example_app/src/main.rs) subdirectory, or read the hosted documentation at [docs.rs/esi](https://docs.rs/esi).

## License

The source and documentation for this project are released under the [MIT License](LICENSE).
