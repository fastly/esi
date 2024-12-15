use crate::{expression::Value, ExecutionError, Result};
use std::convert::TryFrom;

pub fn lower(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(
            "wrong number of arguments to 'lower'".to_string(),
        ));
    }

    Ok(Value::String(args[0].to_string().to_lowercase()))
}

pub fn html_encode(args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        return Err(ExecutionError::FunctionError(
            "wrong number of arguments to 'html_encode'".to_string(),
        ));
    }

    Ok(Value::String(
        html_escape::encode_text(&args[0].to_string()).to_string(),
    ))
}

pub fn replace(args: &[Value]) -> Result<Value> {
    if args.len() < 3 || args.len() > 4 {
        return Err(ExecutionError::FunctionError(
            "wrong number of arguments to 'replace'".to_string(),
        ));
    }
    let Value::String(haystack) = &args[0] else {
        return Err(ExecutionError::FunctionError(
            "incorrect haystack passed to 'replace'".to_string(),
        ));
    };
    let Value::String(needle) = &args[1] else {
        return Err(ExecutionError::FunctionError(
            "incorrect needle passed to 'replace'".to_string(),
        ));
    };
    let Value::String(replacement) = &args[2] else {
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
    Ok(Value::String(haystack.replacen(needle, replacement, count)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lower() {
        match lower(&[Value::String("HELLO".to_string())]) {
            Ok(value) => assert_eq!(value, Value::String("hello".to_string())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }
        match lower(&[Value::String("Rust".to_string())]) {
            Ok(value) => assert_eq!(value, Value::String("rust".to_string())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }
        match lower(&[Value::String("".to_string())]) {
            Ok(value) => assert_eq!(value, Value::String("".to_string())),
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
        match html_encode(&[Value::String("<div>".to_string())]) {
            Ok(value) => assert_eq!(value, Value::String("&lt;div&gt;".to_string())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }
        match html_encode(&[Value::String("&".to_string())]) {
            Ok(value) => assert_eq!(value, Value::String("&amp;".to_string())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        }
        // assert_eq!(
        //     html_encode(&[Value::String('"'.to_string())]),
        //     Value::String("&quot;".to_string())
        // );
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
            Value::String("hello world".to_string()),
            Value::String("world".to_string()),
            Value::String("Rust".to_string()),
        ]) {
            Ok(value) => assert_eq!(value, Value::String("hello Rust".to_string())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        };

        match replace(&[
            Value::String("hello world world".to_string()),
            Value::String("world".to_string()),
            Value::String("Rust".to_string()),
            Value::Integer(1),
        ]) {
            Ok(value) => assert_eq!(value, Value::String("hello Rust world".to_string())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        };

        match replace(&[
            Value::String("hello world world".to_string()),
            Value::String("world".to_string()),
            Value::String("Rust".to_string()),
            Value::Integer(2),
        ]) {
            Ok(value) => assert_eq!(value, Value::String("hello Rust Rust".to_string())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        };

        match replace(&[
            Value::String("hello world".to_string()),
            Value::String("world".to_string()),
            Value::String("Rust".to_string()),
            Value::Integer(usize::MAX as i32),
        ]) {
            Ok(value) => assert_eq!(value, Value::String("hello Rust".to_string())),
            Err(err) => panic!("Unexpected error: {:?}", err),
        };

        match replace(&[
            Value::String("hello world".to_string()),
            Value::String("world".to_string()),
            Value::String("Rust".to_string()),
            Value::String("not an integer".to_string()),
        ]) {
            Ok(_) => panic!("Expected error, but got Ok"),
            Err(err) => assert_eq!(
                err.to_string(),
                ExecutionError::FunctionError("incorrect type passed to 'replace'".to_string())
                    .to_string()
            ),
        };

        match replace(&[
            Value::String("hello world".to_string()),
            Value::String("world".to_string()),
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
