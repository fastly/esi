use crate::expression::Value;
use std::convert::TryFrom;

pub fn lower(args: &[Value]) -> Value {
    if args.len() != 1 {
        return Value::Error("wrong number of arguments to 'lower'".to_string());
    }

    Value::String(args[0].to_string().to_lowercase())
}

pub fn html_encode(args: &[Value]) -> Value {
    if args.len() != 1 {
        return Value::Error("wrong number of arguments to 'html_encode'".to_string());
    }

    Value::String(html_escape::encode_text(&args[0].to_string()).to_string())
}

pub fn replace(args: &[Value]) -> Value {
    if args.len() < 3 {
        return Value::Error("wrong number of arguments to 'replace'".to_string());
    }
    let Value::String(haystack) = &args[0] else {
        return Value::Error("incorrect haystack passed to 'replace'".to_string());
    };
    let Value::String(needle) = &args[1] else {
        return Value::Error("incorrect needle passed to 'replace'".to_string());
    };
    let Value::String(replacement) = &args[2] else {
        return Value::Error("incorrect replacement passed to 'replace'".to_string());
    };

    if args.len() == 4 {
        let Value::Integer(count) = &args[3] else {
            return Value::Error("incorrect type passed to 'replace'".to_string());
        };
        // cap count to usize::MAX
        let count: usize = usize::try_from(*count).unwrap_or(usize::MAX);

        Value::String(haystack.replacen(needle, replacement, count))
    } else {
        Value::String(haystack.replace(needle, replacement))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lower() {
        assert_eq!(
            lower(&[Value::String("HELLO".to_string())]),
            Value::String("hello".to_string())
        );
        assert_eq!(
            lower(&[Value::String("Rust".to_string())]),
            Value::String("rust".to_string())
        );
        assert_eq!(
            lower(&[Value::String("".to_string())]),
            Value::String("".to_string())
        );
        assert_eq!(
            lower(&[Value::Integer(123), Value::Integer(456)]),
            Value::Error("wrong number of arguments to 'lower'".to_string())
        );
    }

    #[test]
    fn test_html_encode() {
        assert_eq!(
            html_encode(&[Value::String("<div>".to_string())]),
            Value::String("&lt;div&gt;".to_string())
        );
        assert_eq!(
            html_encode(&[Value::String("&".to_string())]),
            Value::String("&amp;".to_string())
        );
        // assert_eq!(
        //     html_encode(&[Value::String('"'.to_string())]),
        //     Value::String("&quot;".to_string())
        // );
        assert_eq!(
            html_encode(&[Value::Integer(123), Value::Integer(456)]),
            Value::Error("wrong number of arguments to 'html_encode'".to_string())
        );
    }

    #[test]
    fn test_replace() {
        assert_eq!(
            replace(&[
                Value::String("hello world".to_string()),
                Value::String("world".to_string()),
                Value::String("Rust".to_string())
            ]),
            Value::String("hello Rust".to_string())
        );

        assert_eq!(
            replace(&[
                Value::String("hello world world".to_string()),
                Value::String("world".to_string()),
                Value::String("Rust".to_string()),
                Value::Integer(1)
            ]),
            Value::String("hello Rust world".to_string())
        );

        assert_eq!(
            replace(&[
                Value::String("hello world world".to_string()),
                Value::String("world".to_string()),
                Value::String("Rust".to_string()),
                Value::Integer(2)
            ]),
            Value::String("hello Rust Rust".to_string())
        );

        assert_eq!(
            replace(&[
                Value::String("hello world".to_string()),
                Value::String("world".to_string()),
                Value::String("Rust".to_string()),
                Value::Integer(usize::MAX as i32)
            ]),
            Value::String("hello Rust".to_string())
        );

        assert_eq!(
            replace(&[
                Value::String("hello world".to_string()),
                Value::String("world".to_string()),
                Value::String("Rust".to_string()),
                Value::String("not an integer".to_string())
            ]),
            Value::Error("incorrect type passed to 'replace'".to_string())
        );

        assert_eq!(
            replace(&[
                Value::String("hello world".to_string()),
                Value::String("world".to_string())
            ]),
            Value::Error("wrong number of arguments to 'replace'".to_string())
        );
    }
}
