use crate::{expression::EvalContext, expression::Value, ExecutionError, Result};
use base64::{engine::general_purpose::STANDARD, Engine as _};
use bytes::Bytes;
use chrono::{DateTime, Utc};
use percent_encoding::{percent_decode_str, utf8_percent_encode, NON_ALPHANUMERIC};
use rand::Rng;
use std::cell::RefCell;
use std::rc::Rc;
use std::time::{SystemTime, UNIX_EPOCH};

pub fn lower(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "lower: expected 1 argument, got {}",
            args.len()
        )));
    }

    // If the argument is Null, return Null (don't convert to "null" string)
    if matches!(args[0], Value::Null) {
        return Ok(Value::Null);
    }

    // Fast path: mutate a copy of the bytes in-place for ASCII lowering to avoid String allocs
    if let Value::Text(bytes) = &args[0] {
        let mut buf = bytes.to_vec();
        for b in &mut buf {
            *b = b.to_ascii_lowercase();
        }
        return Ok(Value::Text(buf.into()));
    }

    Ok(Value::Text(args[0].to_string().to_lowercase().into()))
}

pub fn html_encode(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "html_encode: expected 1 argument, got {}",
            args.len()
        )));
    }

    // Per ESI spec: encode only 4 special characters: > < & "
    // html_escape::encode_double_quoted_attribute does exactly this
    let encoded =
        html_escape::encode_double_quoted_attribute(args[0].to_string().as_str()).to_string();
    Ok(Value::Text(encoded.into()))
}

pub fn html_decode(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "html_decode: expected 1 argument, got {}",
            args.len()
        )));
    }

    let decoded = html_escape::decode_html_entities(args[0].to_string().as_str()).to_string();
    Ok(Value::Text(decoded.into()))
}

pub fn convert_to_unicode(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "convert_to_unicode: expected 1 argument, got {}",
            args.len()
        )));
    }

    if let Value::Text(b) = &args[0] {
        return Ok(Value::Text(b.clone()));
    }

    if matches!(args[0], Value::Null) {
        return Ok(Value::Null);
    }

    Ok(Value::Text(args[0].to_string().into()))
}

pub fn convert_from_unicode(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "convert_from_unicode: expected 1 argument, got {}",
            args.len()
        )));
    }

    if let Value::Text(b) = &args[0] {
        return Ok(Value::Text(b.clone()));
    }

    if matches!(args[0], Value::Null) {
        return Ok(Value::Null);
    }

    Ok(Value::Text(args[0].to_string().into()))
}

pub fn set_response_code(args: &[Value], ctx: &mut EvalContext) -> Result<Value> {
    if args.is_empty() || args.len() > 2 {
        return Err(ExecutionError::FunctionError(format!(
            "set_response_code: expected 1-2 arguments, got {}",
            args.len()
        )));
    }

    let status = parse_i32("set_response_code", &args[0])?;
    if !(100..=599).contains(&status) {
        return Err(ExecutionError::FunctionError(
            "set_response_code: invalid status code".to_string(),
        ));
    }

    ctx.set_response_status(status);

    if let Some(body_val) = args.get(1) {
        if matches!(body_val, Value::Null) {
            ctx.set_response_body_override(None);
        } else {
            ctx.set_response_body_override(Some(Bytes::from(body_val.to_string())));
        }
    }

    Ok(Value::Null)
}

pub fn set_redirect(args: &[Value], ctx: &mut EvalContext) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "set_redirect: expected 1 argument, got {}",
            args.len()
        )));
    }

    let location = args[0].to_string();
    ctx.set_response_status(302);
    ctx.add_response_header("Location".to_string(), location);
    ctx.set_response_body_override(None);

    Ok(Value::Null)
}

pub fn upper(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "upper: expected 1 argument, got {}",
            args.len()
        )));
    }

    if matches!(args[0], Value::Null) {
        return Ok(Value::Null);
    }

    // Fast path: mutate a copy of the bytes in-place for ASCII upper to avoid String allocs
    if let Value::Text(bytes) = &args[0] {
        let mut buf = bytes.to_vec();
        for b in &mut buf {
            *b = b.to_ascii_uppercase();
        }
        return Ok(Value::Text(buf.into()));
    }

    Ok(Value::Text(args[0].to_string().to_uppercase().into()))
}

pub fn to_str(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "str: expected 1 argument, got {}",
            args.len()
        )));
    }

    // $str() converts any value to Text so that + does concatenation, not addition.
    // Short-circuit if already Text to avoid a round-trip through String.
    match &args[0] {
        Value::Text(_) => Ok(args[0].clone()),
        Value::Null => Ok(Value::Text(Bytes::new())),
        other => Ok(Value::Text(Bytes::from(other.to_string()))),
    }
}

pub fn lstrip(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "lstrip: expected 1 argument, got {}",
            args.len()
        )));
    }

    if matches!(args[0], Value::Null) {
        return Ok(Value::Null);
    }

    // Zero-copy trim: strip ASCII whitespace directly from bytes
    if let Value::Text(bytes) = &args[0] {
        let start = bytes
            .iter()
            .position(|b| !b.is_ascii_whitespace())
            .unwrap_or(bytes.len());
        return Ok(Value::Text(bytes.slice(start..bytes.len())));
    }

    let s = args[0].to_string();
    Ok(Value::Text(s.trim_start().to_string().into()))
}

pub fn rstrip(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "rstrip: expected 1 argument, got {}",
            args.len()
        )));
    }

    if matches!(args[0], Value::Null) {
        return Ok(Value::Null);
    }

    // Zero-copy trim: strip ASCII whitespace directly from bytes
    if let Value::Text(bytes) = &args[0] {
        let end = bytes
            .iter()
            .rposition(|b| !b.is_ascii_whitespace())
            .map_or(0, |i| i + 1);
        return Ok(Value::Text(bytes.slice(0..end)));
    }

    let s = args[0].to_string();
    Ok(Value::Text(s.trim_end().to_string().into()))
}

pub fn strip(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "strip: expected 1 argument, got {}",
            args.len()
        )));
    }

    if matches!(args[0], Value::Null) {
        return Ok(Value::Null);
    }

    // Zero-copy trim: strip ASCII whitespace directly from bytes
    if let Value::Text(bytes) = &args[0] {
        let start = bytes
            .iter()
            .position(|b| !b.is_ascii_whitespace())
            .unwrap_or(bytes.len());
        let end = bytes
            .iter()
            .rposition(|b| !b.is_ascii_whitespace())
            .map_or(0, |i| i + 1);
        let (s, e) = if start <= end { (start, end) } else { (0, 0) };
        return Ok(Value::Text(bytes.slice(s..e)));
    }

    let s = args[0].to_string();
    Ok(Value::Text(s.trim().to_string().into()))
}

pub fn dollar(args: &[Value]) -> Result<Value> {
    if !args.is_empty() {
        return Err(ExecutionError::FunctionError(format!(
            "dollar: expected 0 arguments, got {}",
            args.len()
        )));
    }

    Ok(Value::Text(Bytes::from("$")))
}

pub fn dquote(args: &[Value]) -> Result<Value> {
    if !args.is_empty() {
        return Err(ExecutionError::FunctionError(format!(
            "dquote: expected 0 arguments, got {}",
            args.len()
        )));
    }

    Ok(Value::Text(Bytes::from("\"")))
}

pub fn squote(args: &[Value]) -> Result<Value> {
    if !args.is_empty() {
        return Err(ExecutionError::FunctionError(format!(
            "squote: expected 0 arguments, got {}",
            args.len()
        )));
    }

    Ok(Value::Text(Bytes::from("'")))
}

pub fn base64_encode(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "base64_encode: expected 1 argument, got {}",
            args.len()
        )));
    }

    let encoded = STANDARD.encode(args[0].to_string().as_bytes());
    Ok(Value::Text(encoded.into()))
}

pub fn base64_decode(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "base64_decode: expected 1 argument, got {}",
            args.len()
        )));
    }

    if matches!(args[0], Value::Null) {
        return Ok(Value::Null);
    }

    let input = args[0].to_string();
    let decoded = STANDARD
        .decode(input.as_bytes())
        .map_err(|_| ExecutionError::FunctionError("base64_decode: invalid base64".to_string()))?;

    // Try to convert to UTF-8 string, but return raw bytes if it fails
    String::from_utf8(decoded.clone()).map_or_else(
        |_| Ok(Value::Text(Bytes::from(decoded))),
        |s| Ok(Value::Text(s.into())),
    )
}

pub fn url_encode(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "url_encode: expected 1 argument, got {}",
            args.len()
        )));
    }

    let encoded = utf8_percent_encode(&args[0].to_string(), NON_ALPHANUMERIC).to_string();
    Ok(Value::Text(encoded.into()))
}

pub fn url_decode(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "url_decode: expected 1 argument, got {}",
            args.len()
        )));
    }

    let input = args[0].to_string();
    let decoded = percent_decode_str(&input)
        .decode_utf8()
        .map_err(|_| ExecutionError::FunctionError("invalid UTF-8 in 'url_decode'".to_string()))?;

    Ok(Value::Text(Bytes::from(decoded.to_string())))
}

fn parse_i32(name: &str, v: &Value) -> Result<i32> {
    match v {
        Value::Integer(i) => Ok(*i),
        Value::Text(b) => std::str::from_utf8(b)
            .ok()
            .and_then(|s| s.trim().parse::<i32>().ok())
            .ok_or_else(|| ExecutionError::FunctionError(format!("{name}: invalid integer"))),
        Value::Null => Ok(0),
        _ => Err(ExecutionError::FunctionError(format!(
            "{name}: invalid integer"
        ))),
    }
}

fn parse_str<'a>(name: &str, v: &'a Value) -> Result<&'a str> {
    if let Value::Text(b) = v {
        std::str::from_utf8(b)
            .map_err(|_| ExecutionError::FunctionError(format!("{name}: invalid string")))
    } else {
        Err(ExecutionError::FunctionError(format!(
            "{name}: invalid string"
        )))
    }
}

pub fn len(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "len: expected 1 argument, got {}",
            args.len()
        )));
    }

    // Per ESI spec, string functions are byte/ASCII-oriented.
    let count = match &args[0] {
        Value::Null => 0,
        Value::Text(b) => b.len() as i32,
        Value::List(items) => items.borrow().len() as i32,
        Value::Dict(map) => map.borrow().len() as i32,
        other => other.to_string().len() as i32,
    };

    Ok(Value::Integer(count))
}

fn parse_positive_bound(name: &str, v: &Value) -> Result<i32> {
    let n = parse_i32(name, v)?;
    if n <= 0 {
        return Err(ExecutionError::FunctionError(format!(
            "{name}: invalid bound"
        )));
    }
    Ok(n)
}

pub fn int(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "int: expected 1 argument, got {}",
            args.len()
        )));
    }

    if let Value::Integer(i) = args[0] {
        return Ok(Value::Integer(i));
    }

    if matches!(args[0], Value::Null) {
        return Ok(Value::Integer(0));
    }

    let parsed = args[0].to_string().trim().parse::<i32>().unwrap_or(0);
    Ok(Value::Integer(parsed))
}

pub fn exists(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "exists: expected 1 argument, got {}",
            args.len()
        )));
    }

    let exists = match &args[0] {
        Value::Null => false,
        Value::Text(b) => !b.is_empty(),
        Value::List(items) => !items.borrow().is_empty(),
        Value::Dict(map) => !map.borrow().is_empty(),
        _ => true,
    };

    Ok(Value::Boolean(exists))
}

pub fn is_empty(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "is_empty: expected 1 argument, got {}",
            args.len()
        )));
    }

    match &args[0] {
        Value::Null => Ok(Value::Boolean(false)),
        Value::Text(b) => Ok(Value::Boolean(b.is_empty())),
        Value::List(items) => Ok(Value::Boolean(items.borrow().is_empty())),
        Value::Dict(map) => Ok(Value::Boolean(map.borrow().is_empty())),
        _ => Ok(Value::Boolean(false)),
    }
}

pub fn index(args: &[Value]) -> Result<Value> {
    if args.len() != 2 {
        return Err(ExecutionError::FunctionError(format!(
            "index: expected 2 arguments, got {}",
            args.len()
        )));
    }

    if matches!(args[0], Value::Null) || matches!(args[1], Value::Null) {
        return Ok(Value::Integer(-1));
    }

    let hay = args[0].to_string();
    let needle = args[1].to_string();

    if needle.is_empty() {
        return Ok(Value::Integer(0));
    }

    // Per ESI spec, string indexing is byte/ASCII-oriented.
    hay.find(&needle).map_or_else(
        || Ok(Value::Integer(-1)),
        |byte_idx| Ok(Value::Integer(byte_idx as i32)),
    )
}

pub fn rindex(args: &[Value]) -> Result<Value> {
    if args.len() != 2 {
        return Err(ExecutionError::FunctionError(format!(
            "rindex: expected 2 arguments, got {}",
            args.len()
        )));
    }

    if matches!(args[0], Value::Null) || matches!(args[1], Value::Null) {
        return Ok(Value::Integer(-1));
    }

    let hay = args[0].to_string();
    let needle = args[1].to_string();

    if needle.is_empty() {
        return Ok(Value::Integer(hay.len() as i32));
    }

    // Per ESI spec, string indexing is byte/ASCII-oriented.
    hay.rfind(&needle).map_or_else(
        || Ok(Value::Integer(-1)),
        |byte_idx| Ok(Value::Integer(byte_idx as i32)),
    )
}

/// $digest_md5(text_to_digest) - Returns MD5 digest as a list of 4 (32 bit) signed integers
pub fn digest_md5(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "digest_md5: expected 1 argument, got {}",
            args.len()
        )));
    }

    if matches!(args[0], Value::Null) {
        return Ok(Value::Null);
    }

    let input = args[0].to_string();
    let digest = md5::compute(input.as_bytes());

    // MD5 produces 128 bits = 16 bytes, which we split into 4 x 32-bit signed integers
    // Convert bytes to i32s (little-endian interpretation)
    let bytes = digest.0;
    let int1 = i32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    let int2 = i32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]);
    let int3 = i32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]);
    let int4 = i32::from_le_bytes([bytes[12], bytes[13], bytes[14], bytes[15]]);

    Ok(Value::List(Rc::new(RefCell::new(vec![
        Value::Integer(int1),
        Value::Integer(int2),
        Value::Integer(int3),
        Value::Integer(int4),
    ]))))
}

/// $digest_md5_hex(text_to_digest) - Returns MD5 digest as a 32 character hex string
pub fn digest_md5_hex(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "digest_md5_hex: expected 1 argument, got {}",
            args.len()
        )));
    }

    if matches!(args[0], Value::Null) {
        return Ok(Value::Null);
    }

    let input = args[0].to_string();
    let digest = md5::compute(input.as_bytes());
    let hex = format!("{digest:x}");
    Ok(Value::Text(hex.into()))
}

pub fn time(args: &[Value]) -> Result<Value> {
    if !args.is_empty() {
        return Err(ExecutionError::FunctionError(format!(
            "time: expected 0 arguments, got {}",
            args.len()
        )));
    }

    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|_| ExecutionError::FunctionError("system time before UNIX_EPOCH".to_string()))?
        .as_secs();

    let clamped = i32::try_from(secs).unwrap_or(i32::MAX);
    Ok(Value::Integer(clamped))
}

pub fn http_time(args: &[Value]) -> Result<Value> {
    if args.len() > 1 {
        return Err(ExecutionError::FunctionError(format!(
            "http_time: expected 0-1 arguments, got {}",
            args.len()
        )));
    }

    let secs = if args.is_empty() || matches!(args[0], Value::Null) {
        Utc::now().timestamp()
    } else {
        i64::from(parse_i32("http_time", &args[0])?)
    };

    let dt = DateTime::<Utc>::from_timestamp(secs, 0)
        .ok_or_else(|| ExecutionError::FunctionError("http_time: invalid timestamp".to_string()))?;

    let formatted = dt.format("%a, %d %b %Y %H:%M:%S GMT").to_string();
    Ok(Value::Text(Bytes::from(formatted)))
}

pub fn strftime(args: &[Value]) -> Result<Value> {
    if args.len() != 2 {
        return Err(ExecutionError::FunctionError(format!(
            "strftime: expected 2 arguments, got {}",
            args.len()
        )));
    }

    let secs = match &args[0] {
        Value::Null => Utc::now().timestamp(),
        v => i64::from(parse_i32("strftime", v)?),
    };

    let fmt = parse_str("strftime", &args[1])?;

    let dt = DateTime::<Utc>::from_timestamp(secs, 0)
        .ok_or_else(|| ExecutionError::FunctionError("strftime: invalid timestamp".to_string()))?;

    Ok(Value::Text(Bytes::from(dt.format(fmt).to_string())))
}

pub fn rand(args: &[Value], ctx: &mut EvalContext) -> Result<Value> {
    let bound = match args.len() {
        0 => 100_000_000i32,
        1 => parse_positive_bound("rand", &args[0])?,
        _ => {
            return Err(ExecutionError::FunctionError(
                "rand expects 0 or 1 argument".to_string(),
            ))
        }
    };

    let mut rng = rand::thread_rng();
    let v: i32 = rng.gen_range(0..bound);
    ctx.set_last_rand(v);
    Ok(Value::Integer(v))
}

pub fn last_rand(args: &[Value], ctx: &EvalContext) -> Result<Value> {
    if !args.is_empty() {
        return Err(ExecutionError::FunctionError(
            "last_rand expects no arguments".to_string(),
        ));
    }

    Ok(ctx.last_rand().map_or_else(|| Value::Null, Value::Integer))
}

pub fn bin_int(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(format!(
            "bin_int: expected 1 argument, got {}",
            args.len()
        )));
    }

    let Value::Integer(value) = args[0] else {
        return Err(ExecutionError::FunctionError(
            "incorrect type passed to 'bin_int'".to_string(),
        ));
    };

    let bytes = value.to_le_bytes();
    Ok(Value::Text(Bytes::copy_from_slice(&bytes)))
}

pub fn substr(args: &[Value]) -> Result<Value> {
    if args.len() < 2 || args.len() > 3 {
        return Err(ExecutionError::FunctionError(format!(
            "substr: expected 2-3 arguments, got {}",
            args.len()
        )));
    }

    if matches!(args[0], Value::Null) {
        return Ok(Value::Null);
    }

    let s = args[0].to_string();
    let Value::Integer(start_i) = args[1] else {
        return Err(ExecutionError::FunctionError(
            "incorrect type for 'substr' start".to_string(),
        ));
    };

    let end_i: Option<i32> = match args.get(2) {
        None => None,
        Some(Value::Integer(j)) => Some(*j),
        Some(_) => {
            return Err(ExecutionError::FunctionError(
                "incorrect type for 'substr' end".to_string(),
            ))
        }
    };

    // Per ESI spec, string indexing is byte/ASCII-oriented.
    let len = s.len() as i32;

    let start = if start_i < 0 {
        (len + start_i).max(0)
    } else {
        start_i.min(len)
    } as usize;

    let end = match end_i {
        None => len,
        Some(j) if j < 0 => (len + j).max(0),
        Some(j) => j.min(len),
    } as usize;

    if end < start {
        return Ok(Value::Text(Bytes::new()));
    }

    Ok(Value::Text(Bytes::copy_from_slice(
        &s.as_bytes()[start..end],
    )))
}

pub fn add_header(args: &[Value], ctx: &mut EvalContext) -> Result<Value> {
    if args.len() != 2 {
        return Err(ExecutionError::FunctionError(format!(
            "add_header: expected 2 arguments, got {}",
            args.len()
        )));
    }

    let name = args[0].to_string();
    let value = args[1].to_string();
    ctx.add_response_header(name, value);

    Ok(Value::Null)
}

pub fn string_split(args: &[Value]) -> Result<Value> {
    if args.is_empty() || args.len() > 3 {
        return Err(ExecutionError::FunctionError(
            "wrong number of arguments to 'string_split'".to_string(),
        ));
    }

    let source = args[0].to_string();
    let sep = match args.get(1) {
        None | Some(Value::Null) => " ".to_string(),
        Some(v) => v.to_string(),
    };

    let max_splits = match args.get(2) {
        None | Some(Value::Null) => None,
        Some(Value::Integer(n)) => Some(*n),
        Some(_) => {
            return Err(ExecutionError::FunctionError(
                "string_split: invalid max_sep".to_string(),
            ))
        }
    };

    // If max_splits is provided and non-positive, do not split
    if let Some(n) = max_splits {
        if n <= 0 {
            return Ok(Value::new_list(vec![Value::Text(source.into())]));
        }
    }

    let parts: Vec<String> = if sep.is_empty() {
        // Empty separator: split into individual bytes (ESI is byte/ASCII-oriented)
        let limit = max_splits.map(|n| n as usize);
        let bytes = source.as_bytes();
        let mut out = Vec::with_capacity(limit.unwrap_or(bytes.len()));

        for (i, &b) in bytes.iter().enumerate() {
            if let Some(limit) = limit {
                if i >= limit {
                    // Remaining bytes as one final element
                    out.push(source[i..].to_string());
                    return Ok(Value::new_list(
                        out.into_iter().map(|s| Value::Text(s.into())).collect(),
                    ));
                }
            }

            out.push(String::from(b as char));
        }

        out
    } else {
        let iter = max_splits.map_or_else(
            || source.split(&sep).map(ToString::to_string).collect(),
            |n| {
                source
                    .splitn(n as usize + 1, &sep)
                    .map(ToString::to_string)
                    .collect()
            },
        );
        iter
    };

    let values = parts.into_iter().map(|s| Value::Text(s.into())).collect();
    Ok(Value::new_list(values))
}

pub fn join(args: &[Value]) -> Result<Value> {
    if args.is_empty() || args.len() > 2 {
        return Err(ExecutionError::FunctionError(format!(
            "join: expected 1-2 arguments, got {}",
            args.len()
        )));
    }

    let sep = match args.get(1) {
        None | Some(Value::Null) => " ".to_string(),
        Some(v) => v.to_string(),
    };

    let Value::List(list_rc) = &args[0] else {
        return Err(ExecutionError::FunctionError(
            "join expects a list as first argument".to_string(),
        ));
    };

    let list = list_rc.borrow();
    let mut out = String::new();
    for (i, v) in list.iter().enumerate() {
        if i > 0 {
            out.push_str(&sep);
        }
        out.push_str(&v.to_string());
    }

    Ok(Value::Text(out.into()))
}

pub fn list_delitem(args: &[Value]) -> Result<Value> {
    if args.len() != 2 {
        return Err(ExecutionError::FunctionError(format!(
            "list_delitem: expected 2 arguments, got {}",
            args.len()
        )));
    }

    let list = match &args[0] {
        Value::List(items) => items.borrow().clone(),
        Value::Null => Vec::new(),
        _ => {
            return Err(ExecutionError::FunctionError(
                "list_delitem expects a list as first argument".to_string(),
            ))
        }
    };

    let idx = parse_i32("list_delitem", &args[1])?;
    if idx < 0 {
        return Ok(Value::new_list(list));
    }

    let mut items = list;
    if (idx as usize) < items.len() {
        items.remove(idx as usize);
    }

    Ok(Value::new_list(items))
}

pub fn replace(args: &[Value]) -> Result<Value> {
    if args.len() < 3 || args.len() > 4 {
        return Err(ExecutionError::FunctionError(format!(
            "replace: expected 3-4 arguments, got {}",
            args.len()
        )));
    }
    let Value::Text(haystack) = &args[0] else {
        return Err(ExecutionError::FunctionError(
            "incorrect haystack passed to 'replace'".to_string(),
        ));
    };
    let Value::Text(needle) = &args[1] else {
        return Err(ExecutionError::FunctionError(
            "incorrect needle passed to 'replace'".to_string(),
        ));
    };
    let Value::Text(replacement) = &args[2] else {
        return Err(ExecutionError::FunctionError(
            "incorrect replacement passed to 'replace'".to_string(),
        ));
    };

    let hay = haystack.as_ref();
    let needle = needle.as_ref();
    let replacement = replacement.as_ref();

    // count is optional, default to usize::MAX; non-positive counts mean "no replacements"
    let count = match args.get(3) {
        Some(Value::Integer(n)) => {
            if *n <= 0 {
                0
            } else {
                *n as usize
            }
        }
        Some(_) => {
            return Err(ExecutionError::FunctionError(
                "incorrect type passed to 'replace'".to_string(),
            ));
        }
        None => usize::MAX,
    };

    if needle.is_empty() {
        return Ok(Value::Text(Bytes::copy_from_slice(hay)));
    }

    let mut out = Vec::with_capacity(hay.len());
    let mut i = 0usize;
    let mut replaced = 0usize;
    while i + needle.len() <= hay.len() {
        if replaced < count && hay[i..i + needle.len()] == *needle {
            out.extend_from_slice(replacement);
            i += needle.len();
            replaced += 1;
        } else {
            out.push(hay[i]);
            i += 1;
        }
    }

    out.extend_from_slice(&hay[i..]);
    Ok(Value::Text(out.into()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_lower() {
        match lower(&[Value::Text("HELLO".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("hello".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }
        match lower(&[Value::Text("Rust".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("rust".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }
        match lower(&[Value::Text("".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }
        match lower(&[Value::Integer(123), Value::Integer(456)]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("lower: expected 1 argument, got 2".to_string())
                    .to_string()
            ),
        }
    }

    #[test]
    fn test_html_encode() {
        // Test that the 4 ESI-specified chars ARE encoded: > < & "
        match html_encode(&[Value::Text("<div>".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("&lt;div&gt;".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }
        match html_encode(&[Value::Text("&".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("&amp;".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }
        match html_encode(&[Value::Text(r#""quoted""#.into())]) {
            Ok(value) => assert_eq!(value, Value::Text("&quot;quoted&quot;".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        };

        // Test that ONLY the 4 ESI-specified chars are encoded (no false positives)
        match html_encode(&[Value::Text("hello'world".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("hello'world".into())), // ' should NOT be encoded
            Err(err) => panic!("Unexpected error: {:?}", err),
        };
        match html_encode(&[Value::Text("café".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("café".into())), // Unicode should NOT be encoded
            Err(err) => panic!("Unexpected error: {:?}", err),
        };
        match html_encode(&[Value::Text("line1\nline2\ttab".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("line1\nline2\ttab".into())), // Whitespace should NOT be encoded
            Err(err) => panic!("Unexpected error: {:?}", err),
        };
        match html_encode(&[Value::Text("@#$%+=?/".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("@#$%+=?/".into())), // Special chars should NOT be encoded
            Err(err) => panic!("Unexpected error: {:?}", err),
        };
        match html_encode(&[Value::Text("123 456".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("123 456".into())), // Numbers and spaces should NOT be encoded
            Err(err) => panic!("Unexpected error: {:?}", err),
        };

        match html_encode(&[Value::Integer(123), Value::Integer(456)]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError(
                    "html_encode: expected 1 argument, got 2".to_string()
                )
                .to_string()
            ),
        }
    }

    #[test]
    fn test_html_decode() {
        match html_decode(&[Value::Text("&lt;div&gt;".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("<div>".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match html_decode(&[Value::Text("foo &amp; bar".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("foo & bar".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match html_decode(&[Value::Text("x".into()), Value::Text("extra".into())]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError(
                    "html_decode: expected 1 argument, got 2".to_string()
                )
                .to_string()
            ),
        }
    }

    #[test]
    fn test_convert_unicode_passthrough() {
        match convert_to_unicode(&[Value::Text("héllo".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("héllo".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match convert_from_unicode(&[Value::Text("héllo".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("héllo".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match convert_to_unicode(&[Value::Null]) {
            Ok(value) => assert_eq!(value, Value::Null),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match convert_from_unicode(&[Value::Null]) {
            Ok(value) => assert_eq!(value, Value::Null),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match convert_to_unicode(&[]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError(
                    "convert_to_unicode: expected 1 argument, got 0".to_string()
                )
                .to_string()
            ),
        }

        match convert_from_unicode(&[Value::Integer(1), Value::Integer(2)]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError(
                    "convert_from_unicode: expected 1 argument, got 2".to_string()
                )
                .to_string()
            ),
        }
    }

    #[test]
    fn test_upper() {
        match upper(&[Value::Text("hello".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("HELLO".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match upper(&[Value::Null]) {
            Ok(value) => assert_eq!(value, Value::Null),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match upper(&[]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("upper: expected 1 argument, got 0".to_string())
                    .to_string()
            ),
        }
    }

    #[test]
    fn test_to_str() {
        match to_str(&[Value::Integer(42)]) {
            Ok(value) => assert_eq!(value, Value::Text("42".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match to_str(&[]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("str: expected 1 argument, got 0".to_string())
                    .to_string()
            ),
        }
    }

    #[test]
    fn test_literal_helpers() {
        match dollar(&[]) {
            Ok(value) => assert_eq!(value, Value::Text("$".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match dollar(&[Value::Text("x".into())]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("dollar: expected 0 arguments, got 1".to_string())
                    .to_string()
            ),
        }

        match dquote(&[]) {
            Ok(value) => assert_eq!(value, Value::Text("\"".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match squote(&[]) {
            Ok(value) => assert_eq!(value, Value::Text("'".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }
    }

    #[test]
    fn test_strip_variants() {
        match lstrip(&[Value::Text("  hello  ".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("hello  ".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match rstrip(&[Value::Text("  hello  ".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("  hello".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match strip(&[Value::Text("  hello  ".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("hello".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match strip(&[Value::Null]) {
            Ok(value) => assert_eq!(value, Value::Null),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match strip(&[]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("strip: expected 1 argument, got 0".to_string())
                    .to_string()
            ),
        }
    }

    #[test]
    fn test_base64_encode() {
        match base64_encode(&[Value::Text("hi".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("aGk=".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match base64_encode(&[]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError(
                    "base64_encode: expected 1 argument, got 0".to_string()
                )
                .to_string()
            ),
        }
    }

    #[test]
    fn test_base64_decode() {
        // Basic decode
        match base64_decode(&[Value::Text("aGk=".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("hi".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        // Decode longer text
        match base64_decode(&[Value::Text("SGVsbG8gV29ybGQh".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("Hello World!".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        // Null handling
        match base64_decode(&[Value::Null]) {
            Ok(value) => assert_eq!(value, Value::Null),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        // Invalid base64
        match base64_decode(&[Value::Text("not-valid-base64!@#".into())]) {
            Ok(_) => panic!("Expected error for invalid base64"),
            Err(err) => assert!(err.to_string().contains("invalid base64")),
        }

        // Wrong argument count
        match base64_decode(&[]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError(
                    "base64_decode: expected 1 argument, got 0".to_string()
                )
                .to_string()
            ),
        }
    }

    #[test]
    fn test_url_encode_decode() {
        match url_encode(&[Value::Text("a b".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("a%20b".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match url_decode(&[Value::Text("a%20b".into())]) {
            Ok(value) => assert_eq!(value, Value::Text("a b".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }
    }

    #[test]
    fn test_exists_is_empty() {
        match exists(&[Value::Text("".into())]) {
            Ok(value) => assert_eq!(value, Value::Boolean(false)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match is_empty(&[Value::Text("".into())]) {
            Ok(value) => assert_eq!(value, Value::Boolean(true)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match exists(&[Value::Null]) {
            Ok(value) => assert_eq!(value, Value::Boolean(false)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match is_empty(&[Value::Null]) {
            Ok(value) => assert_eq!(value, Value::Boolean(false)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match is_empty(&[Value::Text("data".into())]) {
            Ok(value) => assert_eq!(value, Value::Boolean(false)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match exists(&[Value::new_list(vec![Value::Integer(1)])]) {
            Ok(value) => assert_eq!(value, Value::Boolean(true)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match is_empty(&[Value::new_list(Vec::new())]) {
            Ok(value) => assert_eq!(value, Value::Boolean(true)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match exists(&[Value::new_dict(Default::default())]) {
            Ok(value) => assert_eq!(value, Value::Boolean(false)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match exists(&[]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("exists: expected 1 argument, got 0".to_string())
                    .to_string()
            ),
        }

        match is_empty(&[Value::Text("x".into()), Value::Text("y".into())]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("is_empty: expected 1 argument, got 2".to_string())
                    .to_string()
            ),
        }
    }

    #[test]
    fn test_int() {
        match int(&[Value::Text("7".into())]) {
            Ok(value) => assert_eq!(value, Value::Integer(7)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match int(&[Value::Text(" 9 ".into())]) {
            Ok(value) => assert_eq!(value, Value::Integer(9)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match int(&[Value::Text("abc".into())]) {
            Ok(value) => assert_eq!(value, Value::Integer(0)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match int(&[Value::Integer(5)]) {
            Ok(value) => assert_eq!(value, Value::Integer(5)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match int(&[Value::Null]) {
            Ok(value) => assert_eq!(value, Value::Integer(0)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match int(&[Value::Text("1".into()), Value::Text("extra".into())]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("int: expected 1 argument, got 2".to_string())
                    .to_string()
            ),
        }
    }

    #[test]
    fn test_len() {
        match len(&[Value::Text("hello".into())]) {
            Ok(value) => assert_eq!(value, Value::Integer(5)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match len(&[Value::Null]) {
            Ok(value) => assert_eq!(value, Value::Integer(0)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match len(&[Value::new_list(vec![Value::Integer(1), Value::Integer(2)])]) {
            Ok(value) => assert_eq!(value, Value::Integer(2)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match len(&[Value::new_dict(HashMap::from([
            ("a".to_string(), Value::Integer(1)),
            ("b".to_string(), Value::Integer(2)),
        ]))]) {
            Ok(value) => assert_eq!(value, Value::Integer(2)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match len(&[]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("len: expected 1 argument, got 0".to_string())
                    .to_string()
            ),
        }
    }

    #[test]
    fn test_split_join_list_delitem() {
        match string_split(&[Value::Text("a,b,c".into()), Value::Text(",".into())]) {
            Ok(Value::List(items)) => assert_eq!(items.borrow().len(), 3),
            other => panic!("Unexpected result: {:?}", other),
        }

        // default separator (space) and max_splits
        match string_split(&[Value::Text("a b c".into())]) {
            Ok(Value::List(items)) => {
                let items = items.borrow();
                assert_eq!(items.len(), 3);
                assert_eq!(items[0], Value::Text("a".into()));
                assert_eq!(items[1], Value::Text("b".into()));
                assert_eq!(items[2], Value::Text("c".into()));
            }
            other => panic!("Unexpected result: {:?}", other),
        }

        match string_split(&[
            Value::Text("a,b,c,d".into()),
            Value::Text(",".into()),
            Value::Integer(2),
        ]) {
            Ok(Value::List(items)) => {
                let items = items.borrow();
                assert_eq!(items.len(), 3);
                assert_eq!(items[0], Value::Text("a".into()));
                assert_eq!(items[1], Value::Text("b".into()));
                assert_eq!(items[2], Value::Text("c,d".into()));
            }
            other => panic!("Unexpected result: {:?}", other),
        }

        // empty separator splits to chars unless max_splits == 0
        match string_split(&[Value::Text("abc".into()), Value::Text("".into())]) {
            Ok(Value::List(items)) => {
                let joined: String = items.borrow().iter().map(|v| v.to_string()).collect();
                assert_eq!(joined, "abc");
            }
            other => panic!("Unexpected result: {:?}", other),
        }

        match string_split(&[
            Value::Text("abc".into()),
            Value::Text("".into()),
            Value::Integer(0),
        ]) {
            Ok(Value::List(items)) => {
                let items = items.borrow();
                assert_eq!(items.len(), 1);
                assert_eq!(items[0], Value::Text("abc".into()));
            }
            other => panic!("Unexpected result: {other:?}"),
        }

        let list_value = Value::new_list(vec![Value::Text("x".into()), Value::Text("y".into())]);
        match join(&[list_value.clone(), Value::Text("-".into())]) {
            Ok(Value::Text(out)) => assert_eq!(String::from_utf8_lossy(&out), "x-y"),
            other => panic!("Unexpected result: {other:?}"),
        }

        // default separator is space
        match join(std::slice::from_ref(&list_value)) {
            Ok(Value::Text(out)) => assert_eq!(String::from_utf8_lossy(&out), "x y"),
            other => panic!("Unexpected result: {other:?}"),
        }

        match list_delitem(&[list_value, Value::Integer(0)]) {
            Ok(Value::List(items)) => {
                let items = items.borrow();
                assert_eq!(items.len(), 1);
                assert_eq!(items[0], Value::Text("y".into()));
            }
            other => panic!("Unexpected result: {other:?}"),
        }
    }

    #[test]
    fn test_index_rindex() {
        match index(&[
            Value::Text("hello world".into()),
            Value::Text("world".into()),
        ]) {
            Ok(value) => assert_eq!(value, Value::Integer(6)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match rindex(&[Value::Text("ababa".into()), Value::Text("ba".into())]) {
            Ok(value) => assert_eq!(value, Value::Integer(3)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match index(&[Value::Text("abc".into()), Value::Text("z".into())]) {
            Ok(value) => assert_eq!(value, Value::Integer(-1)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match rindex(&[Value::Text("abc".into()), Value::Text("".into())]) {
            Ok(value) => assert_eq!(value, Value::Integer(3)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match index(&[Value::Null, Value::Text("x".into())]) {
            Ok(value) => assert_eq!(value, Value::Integer(-1)),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }
    }

    #[test]
    fn test_bin_int() {
        match bin_int(&[Value::Integer(0x12345678)]) {
            Ok(Value::Text(bytes)) => assert_eq!(bytes.as_ref(), &[0x78, 0x56, 0x34, 0x12]),
            other => panic!("Unexpected result: {:?}", other),
        }

        match bin_int(&[Value::Integer(-1)]) {
            Ok(Value::Text(bytes)) => assert_eq!(bytes.as_ref(), &[0xff, 0xff, 0xff, 0xff]),
            other => panic!("Unexpected result: {:?}", other),
        }

        // Example from spec: X$bin_int(127)X -> 58 7F 00 00 00 58
        let mut rendered = Vec::new();
        rendered.push(b'X');
        match bin_int(&[Value::Integer(127)]) {
            Ok(Value::Text(bytes)) => rendered.extend_from_slice(bytes.as_ref()),
            other => panic!("Unexpected result: {:?}", other),
        }
        rendered.push(b'X');
        assert_eq!(rendered, b"X\x7f\x00\x00\x00X");

        match bin_int(&[Value::Text("not-int".into())]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("incorrect type passed to 'bin_int'".to_string())
                    .to_string()
            ),
        }

        match bin_int(&[]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("bin_int: expected 1 argument, got 0".to_string())
                    .to_string()
            ),
        }
    }

    #[test]
    fn test_digest_md5() {
        // Test that digest_md5 returns a list of 4 signed integers
        match digest_md5(&[Value::Text("hello".into())]) {
            Ok(Value::List(ints)) => {
                let ints = ints.borrow();
                assert_eq!(ints.len(), 4);
                // Expected MD5 for "hello": 5d41402abc4b2a76b9719d911017c592
                // As 4 x i32 little-endian:
                // bytes[0-3]: 5d 41 40 2a -> 0x2a404150
                // bytes[4-7]: bc 4b 2a 76 -> 0x762a4bbc
                // bytes[8-11]: b9 71 9d 91 -> 0x919d71b9
                // bytes[12-15]: 10 17 c5 92 -> 0x92c51710
                assert!(matches!(ints[0], Value::Integer(_)));
                assert!(matches!(ints[1], Value::Integer(_)));
                assert!(matches!(ints[2], Value::Integer(_)));
                assert!(matches!(ints[3], Value::Integer(_)));
            }
            other => panic!("Expected list of 4 integers, got: {:?}", other),
        }

        match digest_md5(&[Value::Null]) {
            Ok(value) => assert_eq!(value, Value::Null),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match digest_md5(&[]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("digest_md5: expected 1 argument, got 0".to_string())
                    .to_string()
            ),
        }
    }

    #[test]
    fn test_digest_md5_hex() {
        // Test that digest_md5_hex returns a 32 character hex string
        match digest_md5_hex(&[Value::Text("hello".into())]) {
            Ok(value) => assert_eq!(
                value,
                Value::Text("5d41402abc4b2a76b9719d911017c592".into())
            ),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match digest_md5_hex(&[Value::Null]) {
            Ok(value) => assert_eq!(value, Value::Null),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        match digest_md5_hex(&[]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError(
                    "digest_md5_hex: expected 1 argument, got 0".to_string()
                )
                .to_string()
            ),
        }
    }

    #[test]
    fn test_time() {
        match time(&[]) {
            Ok(Value::Integer(n)) => assert!(n > 0),
            other => panic!("Unexpected result: {:?}", other),
        }

        match time(&[Value::Integer(1)]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("time: expected 0 arguments, got 1".to_string())
                    .to_string()
            ),
        }
    }

    #[test]
    fn test_http_time() {
        match http_time(&[]) {
            Ok(Value::Text(s)) => {
                let trimmed = String::from_utf8_lossy(&s).trim().to_string();
                assert!(trimmed.ends_with("GMT"));
                chrono::DateTime::parse_from_rfc2822(&trimmed).unwrap();
            }
            other => panic!("Unexpected result: {:?}", other),
        }

        match http_time(&[Value::Integer(0)]) {
            Ok(Value::Text(s)) => {
                assert_eq!(String::from_utf8_lossy(&s), "Thu, 01 Jan 1970 00:00:00 GMT");
            }
            other => panic!("Unexpected result: {:?}", other),
        }

        match http_time(&[Value::Text("x".into())]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("http_time: invalid integer".to_string()).to_string()
            ),
        }
    }

    #[test]
    fn test_strftime() {
        match strftime(&[Value::Integer(0), Value::Text("%Y-%m-%d".into())]) {
            Ok(Value::Text(s)) => assert_eq!(String::from_utf8_lossy(&s), "1970-01-01"),
            other => panic!("Unexpected result: {:?}", other),
        }

        // Test with the Akamai spec example format: $strftime($time(), '%a, %d %B %Y %H:%M:%S %Z')
        // Using timestamp 994867136 = Wed, 11 July 2001 15:58:56 UTC
        match strftime(&[
            Value::Integer(994867136),
            Value::Text("%a, %d %B %Y %H:%M:%S %Z".into()),
        ]) {
            Ok(Value::Text(s)) => {
                assert_eq!(
                    String::from_utf8_lossy(&s),
                    "Wed, 11 July 2001 15:58:56 UTC"
                );
            }
            other => panic!("Unexpected result: {:?}", other),
        }

        match strftime(&[Value::Integer(0)]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("strftime: expected 2 arguments, got 1".to_string())
                    .to_string()
            ),
        }

        match strftime(&[Value::Text("abc".into()), Value::Text("%Y".into())]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("strftime: invalid integer".to_string()).to_string()
            ),
        }

        match strftime(&[Value::Integer(1), Value::Integer(1)]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("strftime: invalid string".to_string()).to_string()
            ),
        }
    }

    #[test]
    fn test_rand_last_rand() {
        let mut ctx = EvalContext::new();

        match last_rand(&[], &ctx) {
            Ok(Value::Null) => {}
            other => panic!("Unexpected result: {:?}", other),
        }

        let first = match rand(&[], &mut ctx) {
            Ok(Value::Integer(v)) => v,
            other => panic!("Unexpected result: {:?}", other),
        };
        assert!((0..100_000_000).contains(&first));

        match last_rand(&[], &ctx) {
            Ok(Value::Integer(v)) => assert_eq!(v, first),
            other => panic!("Unexpected result: {:?}", other),
        }

        let second = match rand(&[Value::Integer(10)], &mut ctx) {
            Ok(Value::Integer(v)) => v,
            other => panic!("Unexpected result: {:?}", other),
        };
        assert!((0..10).contains(&second));

        match last_rand(&[], &ctx) {
            Ok(Value::Integer(v)) => assert_eq!(v, second),
            other => panic!("Unexpected result: {:?}", other),
        }

        match rand(&[Value::Integer(0)], &mut ctx) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("rand: invalid bound".to_string()).to_string()
            ),
        }

        match last_rand(&[Value::Integer(1)], &ctx) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("last_rand expects no arguments".to_string())
                    .to_string()
            ),
        }
    }

    #[test]
    fn test_substr() {
        let s = Value::Text("whether tis nobler in the mind".into());

        // start/end indices (end exclusive)
        match substr(&[s.clone(), Value::Integer(0), Value::Integer(7)]) {
            Ok(value) => assert_eq!(value, Value::Text("whether".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        // example: pick range that yields "nobler"
        match substr(&[s.clone(), Value::Integer(12), Value::Integer(18)]) {
            Ok(value) => assert_eq!(value, Value::Text("nobler".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        // omit end -> to end
        match substr(&[s.clone(), Value::Integer(22)]) {
            Ok(value) => assert_eq!(value, Value::Text("the mind".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        // negative end: drop last 5 chars
        match substr(&[s.clone(), Value::Integer(0), Value::Integer(-5)]) {
            Ok(value) => assert_eq!(value, Value::Text("whether tis nobler in the".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        // negative start, length to end
        match substr(&[s.clone(), Value::Integer(-8)]) {
            Ok(value) => assert_eq!(value, Value::Text("the mind".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        // negative start and negative end window
        match substr(&[s, Value::Integer(-8), Value::Integer(-4)]) {
            Ok(value) => assert_eq!(value, Value::Text("the ".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }
    }

    #[test]
    fn test_add_header_stub() {
        let mut ctx = EvalContext::new();
        match add_header(
            &[Value::Text("Name".into()), Value::Text("Value".into())],
            &mut ctx,
        ) {
            Ok(value) => assert_eq!(value, Value::Null),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }

        assert_eq!(
            ctx.response_headers(),
            [("Name".to_string(), "Value".to_string())]
        );

        match add_header(&[Value::Text("OnlyOneArg".into())], &mut ctx) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError(
                    "add_header: expected 2 arguments, got 1".to_string()
                )
                .to_string()
            ),
        }
    }

    #[test]
    fn test_replace() {
        match replace(&[
            Value::Text("hello world".into()),
            Value::Text("world".into()),
            Value::Text("Rust".into()),
        ]) {
            Ok(value) => assert_eq!(value, Value::Text("hello Rust".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        };

        // match spec example: first occurrence only
        match replace(&[
            Value::Text("abcdefabcde".into()),
            Value::Text("abc".into()),
            Value::Text("xyz".into()),
            Value::Integer(1),
        ]) {
            Ok(value) => assert_eq!(value, Value::Text("xyzdefabcde".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        };

        // zero or negative maxsplit -> no replacements
        match replace(&[
            Value::Text("abc".into()),
            Value::Text("a".into()),
            Value::Text("z".into()),
            Value::Integer(0),
        ]) {
            Ok(value) => assert_eq!(value, Value::Text("abc".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        };
        match replace(&[
            Value::Text("abc".into()),
            Value::Text("a".into()),
            Value::Text("z".into()),
            Value::Integer(-3),
        ]) {
            Ok(value) => assert_eq!(value, Value::Text("abc".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        };

        match replace(&[
            Value::Text("hello world world".into()),
            Value::Text("world".into()),
            Value::Text("Rust".into()),
            Value::Integer(1),
        ]) {
            Ok(value) => assert_eq!(value, Value::Text("hello Rust world".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        };

        match replace(&[
            Value::Text("hello world world".into()),
            Value::Text("world".into()),
            Value::Text("Rust".into()),
            Value::Integer(2),
        ]) {
            Ok(value) => assert_eq!(value, Value::Text("hello Rust Rust".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        };

        match replace(&[
            Value::Text("hello world".into()),
            Value::Text("world".into()),
            Value::Text("Rust".into()),
            Value::Integer(i32::MAX),
        ]) {
            Ok(value) => assert_eq!(value, Value::Text("hello Rust".into())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        };

        match replace(&[
            Value::Text("hello world".into()),
            Value::Text("world".into()),
            Value::Text("Rust".into()),
            Value::Text("not an integer".into()),
        ]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("incorrect type passed to 'replace'".to_string())
                    .to_string()
            ),
        };

        match replace(&[
            Value::Text("hello world".into()),
            Value::Text("world".into()),
        ]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("replace: expected 3-4 arguments, got 2".to_string())
                    .to_string()
            ),
        };
    }

    #[test]
    fn test_set_response_code_and_redirect() {
        let mut ctx = EvalContext::new();

        match set_response_code(&[Value::Integer(404)], &mut ctx) {
            Ok(Value::Null) => {}
            other => panic!("Unexpected result: {:?}", other),
        }
        assert_eq!(ctx.response_status(), Some(404));
        assert!(ctx.response_body_override().is_none());

        match set_response_code(
            &[Value::Integer(500), Value::Text("error body".into())],
            &mut ctx,
        ) {
            Ok(Value::Null) => {}
            other => panic!("Unexpected result: {:?}", other),
        }
        assert_eq!(ctx.response_status(), Some(500));
        assert_eq!(
            ctx.response_body_override()
                .map(|b| String::from_utf8_lossy(b.as_ref()).to_string()),
            Some("error body".to_string())
        );

        match set_response_code(&[Value::Integer(99)], &mut ctx) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("set_response_code: invalid status code".to_string())
                    .to_string()
            ),
        }

        match set_response_code(&[], &mut ctx) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError(
                    "set_response_code: expected 1-2 arguments, got 0".to_string()
                )
                .to_string()
            ),
        }

        match set_redirect(&[Value::Text("http://example.com".into())], &mut ctx) {
            Ok(Value::Null) => {}
            other => panic!("Unexpected result: {:?}", other),
        }
        assert_eq!(ctx.response_status(), Some(302));
        assert_eq!(
            ctx.response_headers().last(),
            Some(&("Location".to_string(), "http://example.com".to_string()))
        );
        assert!(ctx.response_body_override().is_none());

        match set_redirect(
            &[Value::Text("a".into()), Value::Text("b".into())],
            &mut ctx,
        ) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError(
                    "set_redirect: expected 1 argument, got 2".to_string()
                )
                .to_string()
            ),
        }
    }
}
