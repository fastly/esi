use bytes::Bytes;
use fastly::http::Method;
use fastly::Request;
use regex::RegexBuilder;
use std::{collections::HashMap, fmt::Display};

use crate::{
    functions,
    parser_types::{Element, Expr, Operator},
    ExecutionError, Result,
};

/// Evaluates a nom-parsed expression directly without re-lexing/parsing
///
/// This function takes an expression that was already parsed by the nom parser
/// and evaluates it using the full expression evaluator, supporting all operators,
/// comparisons, and functions.
///
/// # Arguments
/// * `expr` - The parsed expression from nom parser
/// * `ctx` - Evaluation context containing variables and state
///
/// # Returns
/// * `Result<Value>` - The evaluated expression result or an error
pub fn eval_expr(expr: &Expr, ctx: &mut EvalContext) -> Result<Value> {
    match expr {
        Expr::Integer(i) => Ok(Value::Integer(*i)),
        Expr::String(Some(s)) => Ok(Value::Text(Bytes::from(s.clone()))),
        Expr::String(None) => Ok(Value::Text(Bytes::new())),
        Expr::Variable(name, key, default) => {
            // Evaluate the key expression if present
            let evaluated_key = if let Some(key_expr) = key {
                let key_result = eval_expr(key_expr, ctx)?;
                Some(key_result.to_string())
            } else {
                None
            };

            let value = ctx.get_variable(name, evaluated_key.as_deref());

            // If value is Null and we have a default, evaluate and use the default
            if matches!(value, Value::Null) {
                if let Some(default_expr) = default {
                    return eval_expr(default_expr, ctx);
                }
            }

            Ok(value)
        }
        Expr::Comparison {
            left,
            operator,
            right,
        } => {
            let left_val = eval_expr(left, ctx)?;
            let right_val = eval_expr(right, ctx)?;
            eval_comparison(&left_val, &right_val, operator, ctx)
        }
        Expr::Call(func_name, args) => {
            let mut values = Vec::new();
            for arg in args {
                values.push(eval_expr(arg, ctx)?);
            }
            call_dispatch(func_name, &values, ctx)
        }
        Expr::Not(expr) => {
            let inner_value = eval_expr(expr, ctx)?;
            Ok(Value::Boolean(!inner_value.to_bool()))
        }
        Expr::DictLiteral(pairs) => {
            let mut map = HashMap::new();
            for (key_expr, val_expr) in pairs {
                let key = eval_expr(key_expr, ctx)?;
                let val = eval_expr(val_expr, ctx)?;
                map.insert(key.to_string(), val);
            }
            Ok(Value::Dict(map))
        }
        Expr::ListLiteral(items) => {
            let mut values = Vec::new();
            for item_expr in items {
                values.push(eval_expr(item_expr, ctx)?);
            }
            Ok(Value::List(values))
        }
        Expr::Interpolated(elements) => {
            // Evaluate each element and concatenate the results
            // This handles compound expressions like: prefix$(VAR)suffix
            let mut result = String::new();
            for element in elements {
                match element {
                    Element::Text(text) => {
                        result.push_str(&String::from_utf8_lossy(text.as_ref()));
                    }
                    Element::Html(html) => {
                        result.push_str(&String::from_utf8_lossy(html.as_ref()));
                    }
                    Element::Expr(expr) => {
                        let value = eval_expr(expr, ctx)?;
                        result.push_str(&value.to_string());
                    }
                    Element::Esi(_) => {
                        // ESI tags in interpolated expressions should not happen
                        // but if they do, ignore them
                    }
                }
            }
            Ok(Value::Text(Bytes::from(result)))
        }
    }
}

/// Evaluates a comparison/operator expression
///
/// This helper function handles all binary operators including comparison, logical,
/// arithmetic, string matching, and containment operators. It applies the appropriate
/// evaluation logic based on the operator type and operand values.
///
/// # Arguments
/// * `left_val` - The evaluated left operand
/// * `right_val` - The evaluated right operand
/// * `operator` - The operator to apply
/// * `ctx` - Evaluation context (needed for regex captures)
///
/// # Returns
/// * `Result<Value>` - The result of applying the operator
fn eval_comparison(
    left_val: &Value,
    right_val: &Value,
    operator: &Operator,
    ctx: &mut EvalContext,
) -> Result<Value> {
    match operator {
        Operator::Matches | Operator::MatchesInsensitive => {
            let test = left_val.to_string();
            let pattern = right_val.to_string();

            let re = if *operator == Operator::Matches {
                RegexBuilder::new(&pattern).build()?
            } else {
                RegexBuilder::new(&pattern).case_insensitive(true).build()?
            };

            if let Some(captures) = re.captures(&test) {
                for (i, cap) in captures.iter().enumerate() {
                    let capval = cap.map_or(Value::Null, |s| {
                        Value::Text(Bytes::from(s.as_str().to_string()))
                    });
                    ctx.set_variable(&ctx.match_name.clone(), Some(&i.to_string()), capval)?;
                }
                Ok(Value::Boolean(true))
            } else {
                Ok(Value::Boolean(false))
            }
        }
        Operator::Has => {
            let haystack = left_val.to_string();
            let needle = right_val.to_string();
            Ok(Value::Boolean(haystack.contains(&needle)))
        }
        Operator::HasInsensitive => {
            let haystack = left_val.to_string().to_lowercase();
            let needle = right_val.to_string().to_lowercase();
            Ok(Value::Boolean(haystack.contains(&needle)))
        }
        Operator::Equals => {
            // Try numeric comparison first, then string comparison
            if let (Value::Integer(l), Value::Integer(r)) = (left_val, right_val) {
                Ok(Value::Boolean(l == r))
            } else {
                Ok(Value::Boolean(
                    left_val.to_string() == right_val.to_string(),
                ))
            }
        }
        Operator::NotEquals => {
            if let (Value::Integer(l), Value::Integer(r)) = (left_val, right_val) {
                Ok(Value::Boolean(l != r))
            } else {
                Ok(Value::Boolean(
                    left_val.to_string() != right_val.to_string(),
                ))
            }
        }
        Operator::LessThan => {
            if let (Value::Integer(l), Value::Integer(r)) = (left_val, right_val) {
                Ok(Value::Boolean(l < r))
            } else {
                Ok(Value::Boolean(left_val.to_string() < right_val.to_string()))
            }
        }
        Operator::LessThanOrEqual => {
            if let (Value::Integer(l), Value::Integer(r)) = (left_val, right_val) {
                Ok(Value::Boolean(l <= r))
            } else {
                Ok(Value::Boolean(
                    left_val.to_string() <= right_val.to_string(),
                ))
            }
        }
        Operator::GreaterThan => {
            if let (Value::Integer(l), Value::Integer(r)) = (left_val, right_val) {
                Ok(Value::Boolean(l > r))
            } else {
                Ok(Value::Boolean(left_val.to_string() > right_val.to_string()))
            }
        }
        Operator::GreaterThanOrEqual => {
            if let (Value::Integer(l), Value::Integer(r)) = (left_val, right_val) {
                Ok(Value::Boolean(l >= r))
            } else {
                Ok(Value::Boolean(
                    left_val.to_string() >= right_val.to_string(),
                ))
            }
        }
        Operator::And => Ok(Value::Boolean(left_val.to_bool() && right_val.to_bool())),
        Operator::Or => Ok(Value::Boolean(left_val.to_bool() || right_val.to_bool())),
        // Arithmetic operators
        Operator::Add => {
            // Try numeric addition first, then string concatenation
            if let (Value::Integer(l), Value::Integer(r)) = (left_val, right_val) {
                Ok(Value::Integer(l + r))
            } else {
                // String/list concatenation
                let result = format!("{left_val}{right_val}");
                Ok(Value::Text(Bytes::from(result)))
            }
        }
        Operator::Subtract => {
            if let (Value::Integer(l), Value::Integer(r)) = (left_val, right_val) {
                Ok(Value::Integer(l - r))
            } else {
                Err(ExecutionError::ExpressionError(
                    "Subtraction requires numeric operands".to_string(),
                ))
            }
        }
        Operator::Multiply => {
            if let (Value::Integer(l), Value::Integer(r)) = (left_val, right_val) {
                Ok(Value::Integer(l * r))
            } else {
                // Could implement string repetition here (e.g., 3 * "abc" = "abcabcabc")
                Err(ExecutionError::ExpressionError(
                    "Multiplication requires numeric operands".to_string(),
                ))
            }
        }
        Operator::Divide => {
            if let (Value::Integer(l), Value::Integer(r)) = (left_val, right_val) {
                if *r == 0 {
                    Err(ExecutionError::ExpressionError(
                        "Division by zero".to_string(),
                    ))
                } else {
                    Ok(Value::Integer(l / r))
                }
            } else {
                Err(ExecutionError::ExpressionError(
                    "Division requires numeric operands".to_string(),
                ))
            }
        }
        Operator::Modulo => {
            if let (Value::Integer(l), Value::Integer(r)) = (left_val, right_val) {
                if *r == 0 {
                    Err(ExecutionError::ExpressionError(
                        "Modulo by zero".to_string(),
                    ))
                } else {
                    Ok(Value::Integer(l % r))
                }
            } else {
                Err(ExecutionError::ExpressionError(
                    "Modulo requires numeric operands".to_string(),
                ))
            }
        }
    }
}

/// Evaluation context for ESI expression processing
///
/// This context holds all runtime state needed during ESI document processing,
/// including variables, request metadata, response manipulation state, and cache tracking.
/// The context is mutable and updated as ESI directives are processed.
pub struct EvalContext {
    /// User-defined variables set by ESI assign directives
    vars: HashMap<String, Value>,
    /// Name of the variable to store regex match captures (default: "MATCHES")
    match_name: String,
    /// HTTP request metadata (method, path, headers, query params) for variable resolution
    request: Request,
    /// Custom headers to add to the response (set by $add_header function)
    response_headers: Vec<(String, String)>,
    /// Last random value generated by $rand() function (for $last_rand() function)
    last_rand: Option<i32>,
    /// HTTP status code override (set by $set_response_code or $set_redirect functions)
    response_status: Option<i32>,
    /// Complete response body override (set by $set_response_code function)
    response_body_override: Option<Bytes>,
    /// Cached parsed query string parameters (lazy-loaded for performance)
    query_params_cache: std::cell::RefCell<Option<HashMap<String, Vec<Bytes>>>>,
    /// Minimum TTL seen across all cached includes (in seconds) for rendered document cacheability
    min_ttl: Option<u32>,
}
impl Default for EvalContext {
    fn default() -> Self {
        Self {
            vars: HashMap::new(),
            match_name: "MATCHES".to_string(),
            request: Request::new(Method::GET, "http://localhost"),
            response_headers: Vec::new(),
            last_rand: None,
            response_status: None,
            response_body_override: None,
            query_params_cache: std::cell::RefCell::new(None),
            min_ttl: None,
        }
    }
}
impl EvalContext {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn new_with_vars(vars: HashMap<String, Value>) -> Self {
        Self {
            vars,
            match_name: "MATCHES".to_string(),
            request: Request::new(Method::GET, "http://localhost"),
            response_headers: Vec::new(),
            last_rand: None,
            response_status: None,
            response_body_override: None,
            query_params_cache: std::cell::RefCell::new(None),
            min_ttl: None,
        }
    }

    pub fn add_response_header(&mut self, name: String, value: String) {
        self.response_headers.push((name, value));
    }

    pub const fn set_last_rand(&mut self, v: i32) {
        self.last_rand = Some(v);
    }

    pub const fn last_rand(&self) -> Option<i32> {
        self.last_rand
    }

    pub fn response_headers(&self) -> &[(String, String)] {
        &self.response_headers
    }

    pub const fn set_response_status(&mut self, status: i32) {
        self.response_status = Some(status);
    }

    pub const fn response_status(&self) -> Option<i32> {
        self.response_status
    }

    pub fn set_response_body_override(&mut self, body: Option<Bytes>) {
        self.response_body_override = body;
    }

    pub const fn response_body_override(&self) -> Option<&Bytes> {
        self.response_body_override.as_ref()
    }

    fn parse_query_params(&self) -> HashMap<String, Vec<Bytes>> {
        let mut params: HashMap<String, Vec<Bytes>> = HashMap::new();

        if let Some(query) = self.request.get_query_str() {
            for pair in query.split('&') {
                if let Some((key, value)) = pair.split_once('=') {
                    params
                        .entry(key.to_string())
                        .or_default()
                        .push(Bytes::from(value.to_string()));
                } else if !pair.is_empty() {
                    // Handle keys without values (e.g., ?flag)
                    params
                        .entry(pair.to_string())
                        .or_default()
                        .push(Bytes::new());
                }
            }
        }

        params
    }

    fn get_query_params(&self) -> std::cell::Ref<'_, Option<HashMap<String, Vec<Bytes>>>> {
        if self.query_params_cache.borrow().is_none() {
            *self.query_params_cache.borrow_mut() = Some(self.parse_query_params());
        }
        self.query_params_cache.borrow()
    }

    pub fn get_variable(&self, key: &str, subkey: Option<&str>) -> Value {
        match key {
            "REQUEST_METHOD" => Value::Text(self.request.get_method_str().to_string().into()),
            "REQUEST_PATH" => Value::Text(self.request.get_path().to_string().into()),
            "REMOTE_ADDR" => Value::Text(
                self.request
                    .get_client_ip_addr()
                    .map_or_else(String::new, |ip| ip.to_string())
                    .into(),
            ),
            "QUERY_STRING" => {
                let params_ref = self.get_query_params();
                let params = params_ref.as_ref().unwrap();

                subkey.map_or_else(
                    || {
                        // Return Dict of all query params when no subkey specified
                        if params.is_empty() {
                            Value::Null
                        } else {
                            let mut dict = HashMap::new();
                            for (key, values) in params.iter() {
                                let value = match values.len() {
                                    0 => Value::Null,
                                    1 => Value::Text(values[0].clone()),
                                    _ => Value::List(
                                        values.iter().map(|v| Value::Text(v.clone())).collect(),
                                    ),
                                };
                                dict.insert(key.clone(), value);
                            }
                            Value::Dict(dict)
                        }
                    },
                    // Look up the field in parsed params
                    |field| match params.get(field) {
                        None => Value::Null,
                        Some(values) if values.is_empty() => Value::Null,
                        Some(values) if values.len() == 1 => Value::Text(values[0].clone()),
                        Some(values) => {
                            Value::List(values.iter().map(|v| Value::Text(v.clone())).collect())
                        }
                    },
                )
            }
            _ if key.starts_with("HTTP_") => {
                let header = key.strip_prefix("HTTP_").unwrap_or_default();
                self.request.get_header(header).map_or(Value::Null, |h| {
                    let value = h.to_str().unwrap_or_default().to_owned();
                    subkey.map_or_else(
                        || Value::Text(value.clone().into()),
                        |field| {
                            value
                                .split(';')
                                .find_map(|s| {
                                    s.trim()
                                        .split_once('=')
                                        .filter(|(key, _)| *key == field)
                                        .map(|(_, val)| Value::Text(val.to_owned().into()))
                                })
                                .unwrap_or(Value::Null)
                        },
                    )
                })
            }
            _ => {
                let stored = self.vars.get(key).cloned().unwrap_or(Value::Null);
                match subkey {
                    None => stored,
                    Some(sub) => get_subvalue(&stored, sub),
                }
            }
        }
    }

    pub fn set_variable(&mut self, key: &str, subkey: Option<&str>, value: Value) -> Result<()> {
        if matches!(value, Value::Null) {
            return Ok(());
        }

        match subkey {
            None => {
                self.vars.insert(key.to_string(), value);
                Ok(())
            }
            Some(sub) => {
                // If variable exists and is a list with numeric subscript, handle list assignment
                // Otherwise create/use dict (dicts can have numeric string keys)
                let entry = self
                    .vars
                    .entry(key.to_string())
                    .or_insert_with(|| Value::Dict(HashMap::new()));
                set_subvalue(entry, sub, value)
            }
        }
    }

    pub fn set_match_name(&mut self, match_name: &str) {
        self.match_name = match_name.to_string();
    }

    pub fn set_request(&mut self, request: Request) {
        self.request = request;
        // Clear cached query params when request changes
        *self.query_params_cache.borrow_mut() = None;
    }

    pub const fn get_request(&self) -> &Request {
        &self.request
    }

    /// Update the minimum TTL for cache tracking
    pub fn update_cache_min_ttl(&mut self, ttl: u32) {
        self.min_ttl = Some(self.min_ttl.map_or(ttl, |current_min| current_min.min(ttl)));
    }

    /// Get the cache control header value for the rendered document
    pub fn cache_control_header(&self, rendered_ttl: Option<u32>) -> Option<String> {
        let ttl = rendered_ttl.or(self.min_ttl)?;
        Some(format!("public, max-age={ttl}"))
    }
}

impl<const N: usize> From<[(String, Value); N]> for EvalContext {
    fn from(data: [(String, Value); N]) -> Self {
        Self::new_with_vars(HashMap::from(data))
    }
}

fn get_subvalue(parent: &Value, subkey: &str) -> Value {
    if let Ok(idx) = subkey.parse::<usize>() {
        if let Value::List(items) = parent {
            return items.get(idx).cloned().unwrap_or(Value::Null);
        }
    }

    if let Value::Dict(map) = parent {
        return map.get(subkey).cloned().unwrap_or(Value::Null);
    }

    Value::Null
}

fn set_subvalue(parent: &mut Value, subkey: &str, value: Value) -> Result<()> {
    // Check if subscript is a numeric index
    if let Ok(idx) = subkey.parse::<usize>() {
        match parent {
            Value::List(items) => {
                // For existing lists, index must exist - no auto-expansion
                if idx >= items.len() {
                    return Err(ExecutionError::VariableError(format!(
                        "list index {} out of range (list has {} elements)",
                        idx,
                        items.len()
                    )));
                }
                items[idx] = value;
                return Ok(());
            }
            Value::Dict(map) => {
                // For dicts, numeric indices are just string keys - allow creation
                map.insert(subkey.to_string(), value);
                return Ok(());
            }
            _ => {
                // Per ESI spec: cannot create list on the fly
                return Err(ExecutionError::VariableError(
                    "cannot create list on the fly - list must already exist".to_string(),
                ));
            }
        }
    }

    // Non-numeric subscript - dictionary key
    match parent {
        Value::Dict(map) => {
            map.insert(subkey.to_string(), value);
            Ok(())
        }
        Value::List(_) => {
            // Per ESI spec: cannot assign string key to a list
            Err(ExecutionError::VariableError(
                "cannot assign string key to a list".to_string(),
            ))
        }
        _ => {
            // Create new dict for non-numeric keys (per ESI spec, dicts can be created on the fly)
            let mut map = HashMap::new();
            map.insert(subkey.to_string(), value);
            *parent = Value::Dict(map);
            Ok(())
        }
    }
}

/// Represents a value in an ESI expression.
///
/// Values can be of different types:
/// - `Integer`: A 32-bit signed integer
/// - `String`: A UTF-8 string
/// - `Boolean`: A boolean value (true/false)
/// - `List`: A list of values (also used for dict iteration as 2-element lists)
/// - `Dict`: A dictionary/map of string keys to values
/// - `Null`: Represents an absence of value
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Integer(i32),
    Text(Bytes),
    Boolean(bool),
    List(Vec<Value>),
    Dict(HashMap<String, Value>),
    Null,
}

impl Value {
    pub(crate) fn to_bool(&self) -> bool {
        match self {
            &Self::Integer(n) => !matches!(n, 0),
            Self::Text(s) => !s.is_empty(),
            Self::Boolean(b) => *b,
            Self::List(items) => !items.is_empty(),
            Self::Dict(map) => !map.is_empty(),
            &Self::Null => false,
        }
    }

    /// Convert Value to Bytes - zero-copy for Text variant
    pub(crate) fn to_bytes(&self) -> Bytes {
        match self {
            Self::Integer(i) => Bytes::from(i.to_string()),
            Self::Text(b) => b.clone(), // Cheap refcount increment
            Self::Boolean(b) => {
                if *b {
                    Bytes::from_static(b"true")
                } else {
                    Bytes::from_static(b"false")
                }
            }
            Self::List(items) => Bytes::from(items_to_string(items)),
            Self::Dict(map) => Bytes::from(dict_to_string(map)),
            Self::Null => Bytes::new(),
        }
    }
}

impl From<String> for Value {
    fn from(s: String) -> Self {
        Self::Text(Bytes::from(s))
    }
}

impl From<&str> for Value {
    fn from(s: &str) -> Self {
        // Copy the string data into a Bytes buffer
        // This is necessary because we can't guarantee the lifetime of &str
        Self::Text(Bytes::copy_from_slice(s.as_bytes()))
    }
}

impl From<Bytes> for Value {
    fn from(b: Bytes) -> Self {
        Self::Text(b)
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Integer(i) => write!(f, "{}", i),
            Self::Text(b) => write!(f, "{}", String::from_utf8_lossy(b.as_ref())),
            Self::Boolean(b) => write!(f, "{}", if *b { "true" } else { "false" }),
            Self::List(items) => write!(f, "{}", items_to_string(items)),
            Self::Dict(map) => write!(f, "{}", dict_to_string(map)),
            Self::Null => Ok(()), // Empty string for Null
        }
    }
}

fn items_to_string(items: &[Value]) -> String {
    let mut out = String::new();
    for (i, v) in items.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&v.to_string());
    }
    out
}

fn dict_to_string(map: &HashMap<String, Value>) -> String {
    let mut parts: Vec<_> = map.iter().map(|(k, v)| format!("{k}={}", v)).collect();
    parts.sort();
    parts.join("&")
}

fn call_dispatch(identifier: &str, args: &[Value], ctx: &mut EvalContext) -> Result<Value> {
    match identifier {
        "ping" => Ok(Value::Text("pong".into())),
        "lower" => functions::lower(args),
        "upper" => functions::upper(args),
        "html_encode" => functions::html_encode(args),
        "html_decode" => functions::html_decode(args),
        "convert_to_unicode" => functions::convert_to_unicode(args),
        "convert_from_unicode" => functions::convert_from_unicode(args),
        "replace" => functions::replace(args),
        "str" => functions::to_str(args),
        "lstrip" => functions::lstrip(args),
        "rstrip" => functions::rstrip(args),
        "strip" => functions::strip(args),
        "substr" => functions::substr(args),
        "dollar" => functions::dollar(args),
        "dquote" => functions::dquote(args),
        "squote" => functions::squote(args),
        "base64_encode" => functions::base64_encode(args),
        "base64_decode" => functions::base64_decode(args),
        "url_encode" => functions::url_encode(args),
        "url_decode" => functions::url_decode(args),
        "exists" => functions::exists(args),
        "is_empty" => functions::is_empty(args),
        "string_split" => functions::string_split(args),
        "join" => functions::join(args),
        "list_delitem" => functions::list_delitem(args),
        "int" => functions::int(args),
        "len" => functions::len(args),
        "index" => functions::index(args),
        "rindex" => functions::rindex(args),
        "digest_md5" => functions::digest_md5(args),
        "digest_md5_hex" => functions::digest_md5_hex(args),
        "bin_int" => functions::bin_int(args),
        "time" => functions::time(args),
        "http_time" => functions::http_time(args),
        "strftime" => functions::strftime(args),
        "rand" => functions::rand(args, ctx),
        "last_rand" => functions::last_rand(args, ctx),
        "add_header" => functions::add_header(args, ctx),
        "set_response_code" => functions::set_response_code(args, ctx),
        "set_redirect" => functions::set_redirect(args, ctx),
        _ => Err(ExecutionError::FunctionError(format!(
            "unknown function: {identifier}"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Helper function for testing expression evaluation
    // Parses and evaluates a raw expression string
    //
    // # Arguments
    // * `raw_expr` - Raw expression string to evaluate
    // * `ctx` - Evaluation context containing variables and state
    //
    // # Returns
    // * `Result<Value>` - The evaluated expression result or an error
    fn evaluate_expression(raw_expr: &str, ctx: &mut EvalContext) -> Result<Value> {
        let (_, expr) = crate::parser::parse_expression(raw_expr).map_err(|e| {
            ExecutionError::ExpressionError(format!("Failed to parse expression: {e}"))
        })?;
        eval_expr(&expr, ctx).map_err(|e| {
            ExecutionError::ExpressionError(format!(
                "Error occurred during expression evaluation: {e}"
            ))
        })
    }

    #[test]
    fn test_eval_matches_comparison() -> Result<()> {
        let result = evaluate_expression(
            "$(hello) matches '^foo'",
            &mut EvalContext::from([("hello".to_string(), Value::Text("foobar".into()))]),
        )?;
        assert_eq!(result, Value::Boolean(true));
        Ok(())
    }
    #[test]
    fn test_eval_matches_i_comparison() -> Result<()> {
        let result = evaluate_expression(
            "$(hello) matches_i '^foo'",
            &mut EvalContext::from([("hello".to_string(), Value::Text("FOOBAR".into()))]),
        )?;
        assert_eq!(result, Value::Boolean(true));
        Ok(())
    }
    #[test]
    fn test_eval_matches_with_captures() -> Result<()> {
        let ctx = &mut EvalContext::from([("hello".to_string(), Value::Text("foobar".into()))]);

        let result = evaluate_expression("$(hello) matches '^(fo)o'", ctx)?;
        assert_eq!(result, Value::Boolean(true));

        let result = evaluate_expression("$(MATCHES{1})", ctx)?;
        assert_eq!(result, Value::Text("fo".into()));
        Ok(())
    }
    #[test]
    fn test_eval_matches_with_captures_and_match_name() -> Result<()> {
        let ctx = &mut EvalContext::from([("hello".to_string(), Value::Text("foobar".into()))]);

        ctx.set_match_name("my_custom_name");
        let result = evaluate_expression("$(hello) matches '^(fo)o'", ctx)?;
        assert_eq!(result, Value::Boolean(true));

        let result = evaluate_expression("$(my_custom_name{1})", ctx)?;
        assert_eq!(result, Value::Text("fo".into()));
        Ok(())
    }
    #[test]
    fn test_eval_matches_comparison_negative() -> Result<()> {
        let result = evaluate_expression(
            "$(hello) matches '^foo'",
            &mut EvalContext::from([("hello".to_string(), Value::Text("nope".into()))]),
        )?;
        assert_eq!(result, Value::Boolean(false));
        Ok(())
    }
    #[test]
    fn test_eval_function_call() -> Result<()> {
        let result = evaluate_expression("$ping()", &mut EvalContext::new())?;
        assert_eq!(result, Value::Text("pong".into()));
        Ok(())
    }
    #[test]
    fn test_eval_lower_call() -> Result<()> {
        let result = evaluate_expression("$lower('FOO')", &mut EvalContext::new())?;
        assert_eq!(result, Value::Text("foo".into()));
        Ok(())
    }
    #[test]
    fn test_eval_html_encode_call() -> Result<()> {
        let result = evaluate_expression("$html_encode('a > b < c')", &mut EvalContext::new())?;
        assert_eq!(result, Value::Text("a &gt; b &lt; c".into()));
        Ok(())
    }
    #[test]
    fn test_eval_replace_call() -> Result<()> {
        let result = evaluate_expression(
            "$replace('abc-def-ghi-', '-', '==')",
            &mut EvalContext::new(),
        )?;
        assert_eq!(result, Value::Text("abc==def==ghi==".into()));
        Ok(())
    }
    #[test]
    fn test_eval_replace_call_with_empty_string() -> Result<()> {
        let result =
            evaluate_expression("$replace('abc-def-ghi-', '-', '')", &mut EvalContext::new())?;
        assert_eq!(result, Value::Text("abcdefghi".into()));
        Ok(())
    }

    #[test]
    fn test_eval_replace_call_with_count() -> Result<()> {
        let result = evaluate_expression(
            "$replace('abc-def-ghi-', '-', '==', 2)",
            &mut EvalContext::new(),
        )?;
        assert_eq!(result, Value::Text("abc==def==ghi-".into()));
        Ok(())
    }

    #[test]
    fn test_context_nested_vars() {
        let mut ctx = EvalContext::new();
        ctx.set_variable("foo", Some("bar"), Value::Text("baz".into()))
            .unwrap();
        assert_eq!(
            ctx.get_variable("foo", Some("bar")),
            Value::Text("baz".into())
        );

        // Per ESI spec: must create list first, then assign to indices
        ctx.set_variable(
            "arr",
            None,
            Value::List(vec![Value::Null, Value::Null, Value::Null]),
        )
        .unwrap();
        ctx.set_variable("arr", Some("0"), Value::Integer(1))
            .unwrap();
        ctx.set_variable("arr", Some("2"), Value::Integer(3))
            .unwrap();

        match ctx.get_variable("arr", None) {
            Value::List(items) => {
                assert_eq!(items.len(), 3);
                assert_eq!(items[0], Value::Integer(1));
                assert_eq!(items[1], Value::Null);
                assert_eq!(items[2], Value::Integer(3));
            }
            other => panic!("Unexpected value: {:?}", other),
        }

        assert_eq!(ctx.get_variable("arr", Some("1")), Value::Null);
        assert_eq!(ctx.get_variable("arr", Some("2")), Value::Integer(3));
    }

    #[test]
    fn test_list_index_out_of_bounds() {
        let mut ctx = EvalContext::new();
        // Create a list with 3 elements
        ctx.set_variable(
            "colors",
            None,
            Value::List(vec![
                Value::Text("red".into()),
                Value::Text("blue".into()),
                Value::Text("green".into()),
            ]),
        )
        .unwrap();

        // Trying to assign to index 3 should fail (only indices 0, 1, 2 exist)
        let result = ctx.set_variable("colors", Some("3"), Value::Text("yellow".into()));
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("out of range"));
    }

    #[test]
    fn test_cannot_assign_string_key_to_list() {
        let mut ctx = EvalContext::new();
        // Create a list
        ctx.set_variable(
            "mylist",
            None,
            Value::List(vec![Value::Integer(1), Value::Integer(2)]),
        )
        .unwrap();

        // Trying to assign a string key to a list should fail
        let result = ctx.set_variable("mylist", Some("foo"), Value::Text("bar".into()));
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("cannot assign string key to a list"));
    }

    #[test]
    fn test_dict_created_on_fly() {
        let mut ctx = EvalContext::new();
        // Assign to non-existent variable with string key - should create dict
        ctx.set_variable("ages", Some("bob"), Value::Integer(34))
            .unwrap();
        ctx.set_variable("ages", Some("joan"), Value::Integer(28))
            .unwrap();

        // Verify retrieval
        let bob_age = ctx.get_variable("ages", Some("bob"));
        assert_eq!(bob_age, Value::Integer(34), "Should retrieve bob's age");

        let joan_age = ctx.get_variable("ages", Some("joan"));
        assert_eq!(joan_age, Value::Integer(28), "Should retrieve joan's age");

        // Verify the dict itself
        let ages_dict = ctx.get_variable("ages", None);
        if let Value::Dict(map) = ages_dict {
            assert_eq!(map.len(), 2, "Dict should have 2 keys");
            assert_eq!(map.get("bob"), Some(&Value::Integer(34)));
            assert_eq!(map.get("joan"), Some(&Value::Integer(28)));
        } else {
            panic!("ages should be a Dict, got {:?}", ages_dict);
        }
    }

    #[test]
    fn test_eval_get_request_method() -> Result<()> {
        let mut ctx = EvalContext::new();
        let result = evaluate_expression("$(REQUEST_METHOD)", &mut ctx)?;
        assert_eq!(result, Value::Text("GET".into()));
        Ok(())
    }

    #[test]
    fn test_nested_lists() -> Result<()> {
        let mut ctx = EvalContext::new();
        // Test nested list literal: [ 'one', [ 'a', 'x', 'c' ], 'three' ]
        let result = evaluate_expression("[ 'one', [ 'a', 'x', 'c' ], 'three' ]", &mut ctx)?;

        match result {
            Value::List(items) => {
                assert_eq!(items.len(), 3);
                assert_eq!(items[0], Value::Text("one".into()));
                assert_eq!(items[2], Value::Text("three".into()));

                // Check nested list
                match &items[1] {
                    Value::List(nested) => {
                        assert_eq!(nested.len(), 3);
                        assert_eq!(nested[0], Value::Text("a".into()));
                        assert_eq!(nested[1], Value::Text("x".into()));
                        assert_eq!(nested[2], Value::Text("c".into()));
                    }
                    other => panic!("Expected nested list, got {:?}", other),
                }
            }
            other => panic!("Expected list, got {:?}", other),
        }
        Ok(())
    }

    #[test]
    fn test_eval_get_request_path() -> Result<()> {
        let mut ctx = EvalContext::new();
        ctx.set_request(Request::new(Method::GET, "http://localhost/hello/there"));

        let result = evaluate_expression("$(REQUEST_PATH)", &mut ctx)?;
        assert_eq!(result, Value::Text("/hello/there".into()));
        Ok(())
    }
    #[test]
    fn test_eval_get_request_query() -> Result<()> {
        let mut ctx = EvalContext::new();
        ctx.set_request(Request::new(Method::GET, "http://localhost?hello"));

        let result = evaluate_expression("$(QUERY_STRING)", &mut ctx)?;
        // Should return Dict with one entry: "hello" -> empty Text
        match result {
            Value::Dict(map) => {
                assert_eq!(map.len(), 1);
                assert_eq!(map.get("hello"), Some(&Value::Text(Bytes::new())));
            }
            other => panic!("Expected Dict, got {:?}", other),
        }
        Ok(())
    }
    #[test]
    fn test_eval_get_request_query_field() -> Result<()> {
        let mut ctx = EvalContext::new();
        ctx.set_request(Request::new(Method::GET, "http://localhost?hello=goodbye"));

        let result = evaluate_expression("$(QUERY_STRING{'hello'})", &mut ctx)?;
        assert_eq!(result, Value::Text("goodbye".into()));
        let result = evaluate_expression("$(QUERY_STRING{'nonexistent'})", &mut ctx)?;
        assert_eq!(result, Value::Null);
        Ok(())
    }
    #[test]
    fn test_eval_get_request_query_field_unquoted() -> Result<()> {
        let mut ctx = EvalContext::new();
        ctx.set_request(Request::new(Method::GET, "http://localhost?hello=goodbye"));

        let result = evaluate_expression("$(QUERY_STRING{hello})", &mut ctx)?;
        assert_eq!(result, Value::Text("goodbye".into()));
        let result = evaluate_expression("$(QUERY_STRING{nonexistent})", &mut ctx)?;
        assert_eq!(result, Value::Null);
        Ok(())
    }
    #[test]
    fn test_eval_get_request_query_duplicate_params() -> Result<()> {
        let mut ctx = EvalContext::new();
        ctx.set_request(Request::new(
            Method::GET,
            "http://localhost?x=1&x=2&x=3&y=single",
        ));

        // Multiple values for 'x' should return a List
        let result = evaluate_expression("$(QUERY_STRING{x})", &mut ctx)?;
        match result {
            Value::List(items) => {
                assert_eq!(items.len(), 3);
                assert_eq!(items[0], Value::Text("1".into()));
                assert_eq!(items[1], Value::Text("2".into()));
                assert_eq!(items[2], Value::Text("3".into()));
            }
            other => panic!("Expected List, got {:?}", other),
        }

        // Single value for 'y' should return Text
        let result = evaluate_expression("$(QUERY_STRING{y})", &mut ctx)?;
        assert_eq!(result, Value::Text("single".into()));

        // No subkey should return Dict with all params
        let result = evaluate_expression("$(QUERY_STRING)", &mut ctx)?;

        // Verify stringification uses & separator (clone before match to avoid borrow issues)
        let stringified = result.to_string();
        assert!(stringified.contains("&"));
        // The list [1,2,3] stringifies as "1,2,3", so we get "x=1,2,3&y=single" (or reversed due to HashMap)
        assert!(stringified == "x=1,2,3&y=single" || stringified == "y=single&x=1,2,3");

        match result {
            Value::Dict(map) => {
                assert_eq!(map.len(), 2);
                // 'x' should be a list
                match map.get("x") {
                    Some(Value::List(items)) => {
                        assert_eq!(items.len(), 3);
                        assert_eq!(items[0], Value::Text("1".into()));
                        assert_eq!(items[1], Value::Text("2".into()));
                        assert_eq!(items[2], Value::Text("3".into()));
                    }
                    other => panic!("Expected List for 'x', got {:?}", other),
                }
                // 'y' should be text
                assert_eq!(map.get("y"), Some(&Value::Text("single".into())));
            }
            other => panic!("Expected Dict, got {:?}", other),
        }

        Ok(())
    }
    #[test]
    fn test_eval_get_remote_addr() -> Result<()> {
        // This is kind of a useless test as this will always return an empty string.
        let mut ctx = EvalContext::new();
        ctx.set_request(Request::new(Method::GET, "http://localhost?hello"));

        let result = evaluate_expression("$(REMOTE_ADDR)", &mut ctx)?;
        assert_eq!(result, Value::Text("".into()));
        Ok(())
    }
    #[test]
    fn test_eval_get_header() -> Result<()> {
        // This is kind of a useless test as this will always return an empty string.
        let mut ctx = EvalContext::new();
        let mut req = Request::new(Method::GET, "http://localhost");
        req.set_header("host", "hello.com");
        req.set_header("foobar", "baz");
        ctx.set_request(req);

        let result = evaluate_expression("$(HTTP_HOST)", &mut ctx)?;
        assert_eq!(result, Value::Text("hello.com".into()));
        let result = evaluate_expression("$(HTTP_FOOBAR)", &mut ctx)?;
        assert_eq!(result, Value::Text("baz".into()));
        Ok(())
    }
    #[test]
    fn test_eval_get_header_field() -> Result<()> {
        // This is kind of a useless test as this will always return an empty string.
        let mut ctx = EvalContext::new();
        let mut req = Request::new(Method::GET, "http://localhost");
        req.set_header("Cookie", "foo=bar; bar=baz");
        ctx.set_request(req);

        let result = evaluate_expression("$(HTTP_COOKIE{'foo'})", &mut ctx)?;
        assert_eq!(result, Value::Text("bar".into()));
        let result = evaluate_expression("$(HTTP_COOKIE{'bar'})", &mut ctx)?;
        assert_eq!(result, Value::Text("baz".into()));
        let result = evaluate_expression("$(HTTP_COOKIE{'baz'})", &mut ctx)?;
        assert_eq!(result, Value::Null);
        Ok(())
    }
    #[test]
    fn test_logical_operators_with_parentheses() {
        let mut ctx = EvalContext::new();

        // Test (1==1)||('abc'=='def')
        let result = evaluate_expression("(1==1)||('abc'=='def')", &mut ctx).unwrap();
        assert_eq!(result.to_string(), "true");

        // Test (4!=5)&&(4==5)
        let result = evaluate_expression("(4!=5)&&(4==5)", &mut ctx).unwrap();
        assert_eq!(result.to_string(), "false");
    }
    #[test]
    fn test_negation_operations() -> Result<()> {
        let mut ctx = EvalContext::new();

        // Test simple negation
        assert_eq!(
            evaluate_expression("!(1 == 2)", &mut ctx)?,
            Value::Boolean(true)
        );
        assert_eq!(
            evaluate_expression("!(1 == 1)", &mut ctx)?,
            Value::Boolean(false)
        );

        // Test negation with other operators
        assert_eq!(
            evaluate_expression("!('a' <= 'c')", &mut ctx)?,
            Value::Boolean(false)
        );
        // Test double negation
        assert_eq!(
            evaluate_expression("!!(1 == 1)", &mut ctx)?,
            Value::Boolean(true)
        );
        // Test complex logical expressions with parentheses
        assert_eq!(
            evaluate_expression("!((1==1)&&(2==2))", &mut ctx)?,
            Value::Boolean(false)
        );
        assert_eq!(
            evaluate_expression("(!(1==1))||(!(2!=2))", &mut ctx)?,
            Value::Boolean(true)
        );

        Ok(())
    }
    #[test]
    fn test_bool_coercion() -> Result<()> {
        assert!(Value::Boolean(true).to_bool());
        assert!(!Value::Boolean(false).to_bool());
        assert!(Value::Integer(1).to_bool());
        assert!(!Value::Integer(0).to_bool());
        assert!(!Value::Text("".into()).to_bool());
        assert!(Value::Text("hello".into()).to_bool());
        assert!(!Value::Null.to_bool());

        Ok(())
    }
    #[test]
    fn test_numeric_vs_lexicographic_comparison() -> Result<()> {
        // ESI spec: "If both operands are numeric, the expression is evaluated numerically.
        // If either binary operand is non-numeric, both operands are evaluated lexicographically as strings."

        // Both numeric - numeric comparison
        let result = evaluate_expression("5 > 3", &mut EvalContext::new())?;
        assert_eq!(result, Value::Boolean(true));

        let result = evaluate_expression("10 == 10", &mut EvalContext::new())?;
        assert_eq!(result, Value::Boolean(true));

        // Both strings - lexicographic comparison
        let result = evaluate_expression("'5' > '3'", &mut EvalContext::new())?;
        assert_eq!(result, Value::Boolean(true)); // "5" > "3" lexicographically

        let result = evaluate_expression("'10' < '9'", &mut EvalContext::new())?;
        assert_eq!(result, Value::Boolean(true)); // "10" < "9" lexicographically (starts with "1")

        // Mixed (numeric and string) - lexicographic comparison
        // When one operand is numeric and one is string, both are compared as strings
        let mut ctx = EvalContext::new();
        ctx.set_variable("numVar", None, Value::Integer(10))
            .unwrap();
        let result = evaluate_expression("$(numVar) > '9'", &mut ctx)?;
        // "10" > "9" lexicographically = false (because "1" < "9")
        assert_eq!(result, Value::Boolean(false));

        // String versions that look numeric
        let result = evaluate_expression("'10' == '10'", &mut EvalContext::new())?;
        assert_eq!(result, Value::Boolean(true));

        // Per spec: "a version reported as 3.01.23 or 1.05a will not test as a number"
        // These should be treated as strings, not parsed as numbers
        // Store version string in variable and compare - proves it's not parsed as number
        let mut ctx = EvalContext::new();
        ctx.set_variable("version", None, Value::Text("3.01.23".into()))
            .unwrap();
        // Compare "3.01.23" stored as a text value with "3.01.23" literal - should be equal
        // This proves stored text values are not coerced to numbers
        let result = evaluate_expression("$(version) == '3.01.23'", &mut ctx)?;
        assert_eq!(result, Value::Boolean(true));

        // Test that version string comparison is lexicographic, not numeric
        // If parsed as number: 3.01 < 3.2 would be TRUE
        // As string: "3.01.23" < "3.2" is FALSE (lexicographic: after "3.", '0' < '2' is true,
        // but we compare "01.23" vs "2", and "01.23" > "2" because '0' > nothing after '2')
        ctx.set_variable("version", None, Value::Text("3.01.23".into()))
            .unwrap();
        let result = evaluate_expression("$(version) < '3.2'", &mut ctx)?;
        assert_eq!(result, Value::Boolean(true)); // Lexicographic: "3.01.23" < "3.2"

        // Test lexicographic comparison of version strings (not numeric parsing)
        // '2.0' < '10.0' is FALSE lexicographically (because '2' > '1')
        // but would be TRUE if parsed numerically (2.0 < 10.0)
        let result = evaluate_expression("'2.0' < '10.0'", &mut EvalContext::new())?;
        assert_eq!(result, Value::Boolean(false)); // Lexicographic: '2' > '1'

        Ok(())
    }

    #[test]
    fn test_empty_null_undefined_evaluate_to_false() -> Result<()> {
        // ESI spec: "If any operand is empty or undefined, the expression is evaluated to be false."

        // Empty string evaluates to false
        let mut ctx = EvalContext::new();
        ctx.set_variable("empty", None, Value::Text("".into()))
            .unwrap();
        let result = evaluate_expression("$(empty)", &mut ctx)?;
        assert_eq!(result.to_bool(), false);

        // Null evaluates to false
        let result = evaluate_expression("$(nonexistent)", &mut EvalContext::new())?;
        assert_eq!(result, Value::Null);
        assert_eq!(result.to_bool(), false);

        // Empty in logical expressions
        let result = evaluate_expression("'' && 'something'", &mut EvalContext::new())?;
        assert_eq!(result, Value::Boolean(false));

        let result = evaluate_expression("'' || 'something'", &mut EvalContext::new())?;
        assert_eq!(result, Value::Boolean(true));

        // Zero evaluates to false (per to_bool implementation)
        let result = evaluate_expression("0", &mut EvalContext::new())?;
        assert_eq!(result.to_bool(), false);

        let result = evaluate_expression("1", &mut EvalContext::new())?;
        assert_eq!(result.to_bool(), true);

        Ok(())
    }

    #[test]
    fn test_triple_quoted_strings() -> Result<()> {
        // ESI spec: "Single or triple (three single) quotes must be used to delimit string literals"

        // Single quotes
        let result = evaluate_expression("'hello'", &mut EvalContext::new())?;
        assert_eq!(result, Value::Text("hello".into()));

        // Triple quotes
        let result = evaluate_expression("'''hello'''", &mut EvalContext::new())?;
        assert_eq!(result, Value::Text("hello".into()));

        // Triple quotes with single quotes inside
        let result = evaluate_expression("'''it's working'''", &mut EvalContext::new())?;
        assert_eq!(result, Value::Text("it's working".into()));

        // Comparison using triple quotes
        let result = evaluate_expression("'''test''' == 'test'", &mut EvalContext::new())?;
        assert_eq!(result, Value::Boolean(true));

        Ok(())
    }
    #[test]
    fn test_string_coercion() -> Result<()> {
        assert_eq!(Value::Boolean(true).to_string(), "true");
        assert_eq!(Value::Boolean(false).to_string(), "false");
        assert_eq!(Value::Integer(1).to_string(), "1");
        assert_eq!(Value::Integer(0).to_string(), "0");
        assert_eq!(Value::Text("".into()).to_string(), "");
        assert_eq!(Value::Text("hello".into()).to_string(), "hello");
        assert_eq!(Value::Null.to_string(), ""); // Null converts to empty string

        Ok(())
    }
    #[test]
    fn test_get_variable_query_string() {
        let mut ctx = EvalContext::new();
        let req = Request::new(Method::GET, "http://localhost?param=value");
        ctx.set_request(req);

        // Test without subkey - should return Dict
        let result = ctx.get_variable("QUERY_STRING", None);
        match result {
            Value::Dict(map) => {
                assert_eq!(map.len(), 1);
                assert_eq!(map.get("param"), Some(&Value::Text("value".into())));
            }
            other => panic!("Expected Dict, got {:?}", other),
        }

        // Test with subkey
        let result = ctx.get_variable("QUERY_STRING", Some("param"));
        assert_eq!(result, Value::Text("value".into()));

        // Test with non-existent subkey
        let result = ctx.get_variable("QUERY_STRING", Some("nonexistent"));
        assert_eq!(result, Value::Null);
    }
}
