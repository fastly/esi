# ESI for Fastly

This crate provides a streaming Edge Side Includes parser and executor designed for Fastly Compute.

The implementation is a subset of Akamai ESI 5.0 supporting the following tags:

- `<esi:include>` (+ `alt`, `onerror="continue"`)
- `<esi:try>` | `<esi:attempt>` | `<esi:except>`
- `<esi:vars>` | `<esi:assign>` (with subscript support for dict/list assignment)
- `<esi:choose>` | `<esi:when>` | `<esi:otherwise>`
- `<esi:foreach>` | `<esi:break>` (loop over lists and dicts)
- `<esi:comment>`
- `<esi:remove>`

**Note:** The following tags support nested ESI tags: `<esi:try>`, `<esi:attempt>`, `<esi:except>`, `<esi:choose>`, `<esi:when>`, `<esi:otherwise>`, `<esi:foreach>`, and `<esi:assign>` (long form only).

Other tags will be ignored and served to the client as-is.

### Expression Features

- **Integer literals**: `42`, `-10`, `0`
- **String literals**: `'single quoted'`, `"double quoted"`, `'''triple quoted'''`
- **Dict literals**: `{'key1': 'value1', 'key2': 'value2'}`
- **List literals**: `['item1', 'item2', 'item3']`
- **Nested structures**: Lists can be nested: `['one', ['a', 'b', 'c'], 'three']`
- **Subscript assignment**: `<esi:assign name="dict{'key'}" value="val"/>` or `<esi:assign name="list{0}" value="val"/>`
- **Subscript access**: `$(dict{'key'})` or `$(list{0})`
- **Foreach loops**: Iterate over lists or dicts with `<esi:foreach>` and use `<esi:break>` to exit early
- **Comparison operators**: `==`, `!=`, `<`, `>`, `<=`, `>=`, `has`, `has_i`, `matches`, `matches_i`
  - `has` - Case-sensitive substring containment: `$(str) has 'substring'`
  - `has_i` - Case-insensitive substring containment: `$(str) has_i 'substring'`
  - `matches` - Case-sensitive regex matching: `$(str) matches 'pattern'`
  - `matches_i` - Case-insensitive regex matching: `$(str) matches_i 'pattern'`
- **Logical operators**: `&&` (and), `||` (or), `!` (not)

### Function Library

This implementation includes a comprehensive library of ESI functions:

**String Manipulation:**

- `$lower(string)` - Convert to lowercase
- `$upper(string)` - Convert to uppercase
- `$lstrip(string)`, `$rstrip(string)`, `$strip(string)` - Remove whitespace
- `$substr(string, start [, length])` - Extract substring
- `$replace(haystack, needle, replacement [, count])` - Replace occurrences
- `$str(value)` - Convert to string
- `$join(list, separator)` - Join list elements
- `$string_split(string, delimiter [, maxsplit])` - Split string into list

**Encoding/Decoding:**

- `$html_encode(string)`, `$html_decode(string)` - HTML entity encoding
- `$url_encode(string)`, `$url_decode(string)` - URL encoding
- `$base64_encode(string)` - Base64 encoding
- `$convert_to_unicode(string)`, `$convert_from_unicode(string)` - Unicode conversion

**Quote Helpers:**

- `$dollar()` - Returns `$`
- `$dquote()` - Returns `"`
- `$squote()` - Returns `'`

**Type Conversion & Checks:**

- `$int(value)` - Convert to integer
- `$exists(value)` - Check if value exists
- `$is_empty(value)` - Check if value is empty
- `$len(value)` - Get length of string or list

**List Operations:**

- `$list_delitem(list, index)` - Remove item from list
- `$index(string, substring)`, `$rindex(string, substring)` - Find substring position

**Cryptographic:**

- `$md5_digest(string)` - Generate MD5 hash

**Time/Date:**

- `$time()` - Current Unix timestamp
- `$http_time(timestamp)` - Format timestamp as HTTP date
- `$strftime(format, timestamp)` - Format timestamp with custom format
- `$bin_int(binary_string)` - Convert binary string to integer

**Random & Response:**

- `$rand()` - Generate random number
- `$last_rand()` - Get last generated random number

**Response Manipulation:**

These functions modify the HTTP response sent to the client:

- `$add_header(name, value)` - Add a custom response header
  ```html
  <esi:vars>$add_header('X-Custom-Header', 'my-value')</esi:vars>
  ```
- `$set_response_code(code [, body])` - Set HTTP status code and optionally override response body
  ```html
  <esi:vars>$set_response_code(404, 'Page not found')</esi:vars>
  ```
- `$set_redirect(url [, code])` - Set HTTP redirect (default 302)
  ```html
  <esi:vars>$set_redirect('https://example.com/new-location')</esi:vars> <esi:vars>$set_redirect('https://example.com/moved', 301)</esi:vars>
  ```

**Note:** Response manipulation functions are buffered during ESI processing and applied when `process_response()` sends the final response to the client.

## Example Usage

### Streaming Processing (Recommended)

The recommended approach uses streaming to process the document as it arrives, minimizing memory usage and latency:

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
            // Use the default ESI configuration.
            esi::Configuration::default()
        );

        // Stream the ESI response directly to the client
        processor.process_response(
            // The ESI source document. Body will be consumed and streamed.
            &mut beresp,
            // Optionally provide a template for the client response.
            Some(Response::from_status(StatusCode::OK).with_content_type(mime::TEXT_HTML)),
            // Provide logic for sending fragment requests, otherwise the hostname
            // of the request URL will be used as the backend name.
            Some(&|req| {
                println!("Sending request {} {}", req.get_method(), req.get_path());
                Ok(req.with_ttl(120).send_async("mock-s3")?.into())
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
    } else {
        // Otherwise, we can just return the response.
        beresp.send_to_client();
    }

    Ok(())
}
```

### Custom Stream Processing

For advanced use cases, you can process any `BufRead` source and write to any `Write` destination:

```rust,no_run
use std::io::{BufReader, Write};
use esi::{Processor, Configuration};

fn process_custom_stream(
    input: impl std::io::Read,
    output: &mut impl Write,
) -> Result<(), esi::ExecutionError> {
    let mut processor = Processor::new(None, Configuration::default());

    // Process from any readable source
    let reader = BufReader::new(input);

    processor.process_stream(
        reader,
        output,
        Some(&|req| {
            // Custom fragment dispatcher
            Ok(req.send_async("backend")?.into())
        }),
        None,
    )?;

    Ok(())
}
```

See example applications in the [`examples`](./examples) subdirectory or read the hosted documentation at [docs.rs/esi](https://docs.rs/esi). Due to the fact that this processor streams fragments to the client as soon as they are available, it is not possible to return a relevant status code for later errors once we have started streaming the response to the client. For this reason, it is recommended that you refer to the [`esi_example_advanced_error_handling`](./examples/esi_example_advanced_error_handling) application, which allows you to handle errors gracefully by maintaining ownership of the output stream.

## Testing

In order to run the test suite for the packages in this repository, [`viceroy`](https://github.com/fastly/Viceroy) must be available in your PATH. You can install the latest version of `viceroy` by running the following command:

```sh
cargo install viceroy
```

## License

The source and documentation for this project are released under the [MIT License](./LICENSE).
