# ESI for Fastly

This crate provides a streaming Edge Side Includes parser and executor designed for Fastly Compute.

The implementation is a subset of Akamai ESI 5.0 supporting the following tags:

- `<esi:include>`
- `<esi:eval>` - evaluates included content as ESI
- `<esi:try>` | `<esi:attempt>` | `<esi:except>`
- `<esi:vars>` | `<esi:assign>` (with subscript support for dict/list assignment)
- `<esi:choose>` | `<esi:when>` | `<esi:otherwise>`
- `<esi:foreach>` | `<esi:break>` (loop over lists and dicts)
- `<esi:function>` | `<esi:return>` (user-defined functions)
- `<esi:comment>`
- `<esi:remove>`
- `<esi:text>` (raw passthrough — content is emitted verbatim, no ESI processing)

**Note:** The following tags support nested ESI tags: `<esi:try>`, `<esi:attempt>`, `<esi:except>`, `<esi:choose>`, `<esi:when>`, `<esi:otherwise>`, `<esi:foreach>`, `<esi:function>`, and `<esi:assign>` (long form only).

**Dynamic Content Assembly (DCA)**: Both `<esi:include>` and `<esi:eval>` support the `dca` attribute:

- `dca="none"` (default): For `include`, inserts raw content without ESI processing. For `eval`, fragment executes in parent's context (variables shared).
- `dca="esi"`: Two-phase processing: fragment is first processed in an isolated context, then the output is processed in parent's context (variables from phase 1 don't leak, but output can contain ESI tags).

**Include vs Eval**:

- `<esi:include>`: Fetches content from origin
  - `dca="none"`: Inserts content verbatim (no ESI processing)
  - `dca="esi"`: Parses and evaluates content as ESI before insertion
- `<esi:eval>`: Fetches content and **always** parses it as ESI (blocking operation)
  - `dca="none"`: Evaluates in parent's namespace (variables from fragment affect parent)
  - `dca="esi"`: **Two-phase**: Phase 1 processes fragment in isolated context (variables set here stay isolated), then Phase 2 processes the output in parent's context (output can contain ESI that accesses parent variables)

### Include/Eval Attributes

Both `<esi:include>` and `<esi:eval>` support the following attributes:

**Required:**

- `src="url"` - Source URL to fetch (supports ESI expressions)

**Fallback & Error Handling:**

- `alt="url"` - Fallback URL if primary request fails (include only, eval uses try/except)
- `onerror="continue"` - On error, delete the tag with no output (continue processing without failing)

**Content Processing:**

- `dca="none|esi"` - Dynamic Content Assembly mode (default: `none`)
  - `none`: For include, insert content as-is. For eval, process in parent's context (single-phase).
  - `esi`: For include, parse and evaluate as ESI. For eval, two-phase processing: first in isolated context, then output processed in parent context.

**Caching:**

- `ttl="duration"` - Cache time-to-live (e.g., `"120m"`, `"1h"`, `"2d"`, `"0s"` to disable)
- `no-store="true"` - Bypass cache entirely

**Request Configuration:**

- `maxwait="milliseconds"` - Request timeout in milliseconds
- `method="GET|POST"` - HTTP method (default: `GET`)
- `entity="body"` - Request body for POST requests

**Headers:**

- `appendheaders="header:value"` - Append headers to the request
- `removeheaders="header1,header2"` - Remove headers from the request
- `setheaders="header:value"` - Set/replace headers on the request

**Parameters:**

- Nested `<esi:param name="key" value="val"/>` elements append query parameters to the URL

**Example:**

```html
<esi:include src="http://api.example.com/user" alt="http://cache.example.com/user" dca="esi" ttl="5m" maxwait="1000" onerror="continue">
  <esi:param name="id" value="$(user_id)" />
  <esi:param name="format" value="'json'" />
</esi:include>
```

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
- `$base64_encode(string)`, `$base64_decode(string)` - Base64 encoding/decoding
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

- `$digest_md5(string)` - Generate MD5 hash (binary)
- `$digest_md5_hex(string)` - Generate MD5 hash (hex string)

**Time/Date:**

- `$time()` - Current Unix timestamp
- `$http_time(timestamp)` - Format timestamp as HTTP date
- `$strftime(timestamp, format)` - Format timestamp with custom format
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

**Diagnostic:**

- `$ping()` - Returns the string `"pong"` (useful for testing)

**Note:** Response manipulation functions are buffered during ESI processing and applied when `process_response()` sends the final response to the client.

### User-Defined Functions

You can define reusable functions with `<esi:function>` and return values with `<esi:return>`:

```html
<esi:function name="greet">
  <esi:assign name="greeting" value="'Hello, ' + $(ARGS{0}) + '!'" />
  <esi:return value="$(greeting)" />
</esi:function>

<esi:vars>$greet('World')</esi:vars>
```

- `<esi:function name="...">` defines a function; the body can contain any ESI tags.
- `<esi:return value="..."/>` returns a value from the function.
- Inside a function body, `$(ARGS)` is a list of the positional arguments passed to the call, and individual arguments can be accessed with `$(ARGS{0})`, `$(ARGS{1})`, etc.
- Functions support recursion up to the configured depth (default: 5, see [Configuration](#configuration)).
- User-defined functions take priority over built-in functions of the same name.

### Built-in Variables

The following variables are available in ESI expressions:

**Request metadata:**

- `$(REQUEST_METHOD)` - HTTP method of the original client request (e.g. `GET`)
- `$(REQUEST_PATH)` - Path component of the request URL
- `$(QUERY_STRING)` - Raw query string from the request URL
- `$(REMOTE_ADDR)` - Client IP address

**HTTP headers:**

- `$(HTTP_<HEADER>)` - Value of the named request header (e.g. `$(HTTP_HOST)`, `$(HTTP_ACCEPT)`)
- `$(HTTP_COOKIE{'name'})` - Value of a specific cookie from the `Cookie` header

**Regex captures:**

- `$(MATCHES{0})`, `$(MATCHES{1})`, … - Capture groups from the last `matches` / `matches_i` operator or `<esi:when matchname="...">` test

### Configuration

`Configuration` controls the processor's runtime behaviour. All fields have sensible defaults and can be customised with builder methods:

```rust,no_run
let config = esi::Configuration::default()
    .with_escaped(true)                      // unescape HTML entities in URLs (default: true)
    .with_chunk_size(32768)                  // streaming read buffer, in bytes (default: 16384)
    .with_max_function_recursion_depth(10)   // max depth for user-defined function calls (default: 5)
    .with_caching(esi::cache::CacheConfig {
        is_rendered_cacheable: true,
        rendered_cache_control: true,
        rendered_ttl: Some(600),
        is_includes_cacheable: true,
        includes_default_ttl: Some(300),
        includes_force_ttl: None,
    });
```

| Field                      | Builder method                             | Default   | Description                                                                                                                        |
| -------------------------- | ------------------------------------------ | --------- | ---------------------------------------------------------------------------------------------------------------------------------- |
| `is_escaped_content`       | `with_escaped(bool)`                       | `true`    | Unescape HTML entities in URLs. Set to `false` for non-HTML templates (e.g. JSON).                                                 |
| `chunk_size`               | `with_chunk_size(usize)`                   | `16384`   | Size (bytes) of the read buffer used when streaming ESI input. Larger values may improve throughput; smaller values reduce memory. |
| `function_recursion_depth` | `with_max_function_recursion_depth(usize)` | `5`       | Maximum call-stack depth for user-defined ESI functions.                                                                           |
| `cache`                    | `with_caching(CacheConfig)`                | see below | Cache settings for rendered output and included fragments.                                                                         |

**`CacheConfig` fields:**

| Field                    | Default | Description                                                      |
| ------------------------ | ------- | ---------------------------------------------------------------- |
| `is_rendered_cacheable`  | `false` | Whether the final rendered output is cacheable.                  |
| `rendered_cache_control` | `false` | Emit a `Cache-Control` header on the rendered response.          |
| `rendered_ttl`           | `None`  | TTL (seconds) for the rendered response.                         |
| `is_includes_cacheable`  | `false` | Whether individual include responses should be cached.           |
| `includes_default_ttl`   | `None`  | Default TTL (seconds) for cached includes.                       |
| `includes_force_ttl`     | `None`  | Force a specific TTL on all includes, overriding origin headers. |

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
            Some(&|req, _maxwait| {
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
        Some(&|req, _maxwait| {
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
