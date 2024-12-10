use crate::expression::Value;

pub fn lower(args: Vec<Value>) -> Value {
    if args.len() != 1 {
        return Value::Error("wrong number of arguments to 'lower'".to_string());
    }

    Value::String(args[0].to_string().to_lowercase())
}

pub fn html_encode(args: Vec<Value>) -> Value {
    if args.len() != 1 {
        return Value::Error("wrong number of arguments to 'html_encode'".to_string());
    }

    Value::String(html_escape::encode_text(&args[0].to_string()).to_string())
}

pub fn replace(args: Vec<Value>) -> Value {
    if args.len() < 3 {
        return Value::Error("wrong number of arguments to 'replace'".to_string());
    }
    let haystack = &args[0].to_string();
    let needle = &args[1].to_string();
    let replacement = &args[2].to_string();

    if args.len() == 4 {
        let Value::Integer(count) = &args[3] else {
            return Value::Error("incorrect type passed to 'replace'".to_string());
        };
        let count: usize = *count as usize; // TODO: do this more safely

        return Value::String(haystack.replacen(needle, replacement, count));
    } else {
        return Value::String(haystack.replace(needle, replacement));
    }
}
