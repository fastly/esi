use crate::{expression::Value, ExecutionError, Result};
use std::convert::TryFrom;

pub fn lower(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(
            "wrong number of arguments to 'lower'".to_string(),
        ));
    }

    // If the argument is Null, return Null (don't convert to "null" string)
    if matches!(args[0], Value::Null) {
        return Ok(Value::Null);
    }

    Ok(Value::Text(args[0].to_string().to_lowercase().into()))
}

pub fn html_encode(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(
            "wrong number of arguments to 'html_encode'".to_string(),
        ));
    }

    let encoded = html_escape::encode_double_quoted_attribute(&args[0]).to_string();
    Ok(Value::Text(encoded.into()))
}

pub fn replace(args: &[Value]) -> Result<Value> {
    if args.len() < 3 || args.len() > 4 {
        return Err(ExecutionError::FunctionError(
            "wrong number of arguments to 'replace'".to_string(),
        ));
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

    // count is optional, default to usize::MAX
    let count = match args.get(3) {
        Some(Value::Integer(count)) => {
            // cap count to usize::MAX
            let count: usize = usize::try_from(*count).unwrap_or(usize::MAX);
            count
        }
        Some(_) => {
            return Err(ExecutionError::FunctionError(
                "incorrect type passed to 'replace'".to_string(),
            ));
        }
        None => usize::MAX,
    };
    Ok(Value::Text(
        haystack
            .replacen(needle.as_ref(), replacement, count)
            .into(),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

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
                ExecutionError::FunctionError("wrong number of arguments to 'lower'".to_string())
                    .to_string()
            ),
        }
    }

    #[test]
    fn test_html_encode() {
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
        match html_encode(&[Value::Integer(123), Value::Integer(456)]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError(
                    "wrong number of arguments to 'html_encode'".to_string()
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
            Value::Integer(usize::MAX as i32),
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
                ExecutionError::FunctionError("wrong number of arguments to 'replace'".to_string())
                    .to_string()
            ),
        };
    }
}
