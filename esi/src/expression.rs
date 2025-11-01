use fastly::http::Method;
use fastly::Request;
use log::debug;
use regex::RegexBuilder;
use std::borrow::Cow;
use std::{collections::HashMap, fmt::Display};

use crate::{functions, parser_types, ExecutionError, Result};

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
pub fn eval_expr(expr: parser_types::Expr, ctx: &mut EvalContext) -> Result<Value> {
    match expr {
        parser_types::Expr::Integer(i) => Ok(Value::Integer(i)),
        parser_types::Expr::String(Some(s)) => Ok(Value::Text(Cow::Owned(s.to_string()))),
        parser_types::Expr::String(None) => Ok(Value::Text(Cow::Owned(String::new()))),
        parser_types::Expr::Variable(name, key, default) => {
            // Evaluate the key expression if present
            let evaluated_key = if let Some(key_expr) = key {
                let key_result = eval_expr(*key_expr, ctx)?;
                Some(key_result.to_string())
            } else {
                None
            };

            let value = ctx.get_variable(name, evaluated_key.as_deref());

            // If value is Null and we have a default, evaluate and use the default
            if matches!(value, Value::Null) {
                if let Some(default_expr) = default {
                    return eval_expr(*default_expr, ctx);
                }
            }

            Ok(value)
        }
        parser_types::Expr::Comparison {
            left,
            operator,
            right,
        } => {
            let left_val = eval_expr(*left, ctx)?;
            let right_val = eval_expr(*right, ctx)?;

            match operator {
                parser_types::Operator::Matches | parser_types::Operator::MatchesInsensitive => {
                    let test = left_val.to_string();
                    let pattern = right_val.to_string();

                    let re = if operator == parser_types::Operator::Matches {
                        RegexBuilder::new(&pattern).build()?
                    } else {
                        RegexBuilder::new(&pattern).case_insensitive(true).build()?
                    };

                    if let Some(captures) = re.captures(&test) {
                        for (i, cap) in captures.iter().enumerate() {
                            let capval = cap.map_or(Value::Null, |s| {
                                Value::Text(Cow::Owned(s.as_str().into()))
                            });
                            ctx.set_variable(&ctx.match_name.clone(), Some(&i.to_string()), capval);
                        }
                        Ok(Value::Boolean(true))
                    } else {
                        Ok(Value::Boolean(false))
                    }
                }
                parser_types::Operator::Equals => {
                    // Try numeric comparison first, then string comparison
                    if let (Value::Integer(l), Value::Integer(r)) = (&left_val, &right_val) {
                        Ok(Value::Boolean(l == r))
                    } else {
                        Ok(Value::Boolean(
                            left_val.to_string() == right_val.to_string(),
                        ))
                    }
                }
                parser_types::Operator::NotEquals => {
                    if let (Value::Integer(l), Value::Integer(r)) = (&left_val, &right_val) {
                        Ok(Value::Boolean(l != r))
                    } else {
                        Ok(Value::Boolean(
                            left_val.to_string() != right_val.to_string(),
                        ))
                    }
                }
                parser_types::Operator::LessThan => {
                    if let (Value::Integer(l), Value::Integer(r)) = (&left_val, &right_val) {
                        Ok(Value::Boolean(l < r))
                    } else {
                        Ok(Value::Boolean(left_val.to_string() < right_val.to_string()))
                    }
                }
                parser_types::Operator::LessThanOrEqual => {
                    if let (Value::Integer(l), Value::Integer(r)) = (&left_val, &right_val) {
                        Ok(Value::Boolean(l <= r))
                    } else {
                        Ok(Value::Boolean(
                            left_val.to_string() <= right_val.to_string(),
                        ))
                    }
                }
                parser_types::Operator::GreaterThan => {
                    if let (Value::Integer(l), Value::Integer(r)) = (&left_val, &right_val) {
                        Ok(Value::Boolean(l > r))
                    } else {
                        Ok(Value::Boolean(left_val.to_string() > right_val.to_string()))
                    }
                }
                parser_types::Operator::GreaterThanOrEqual => {
                    if let (Value::Integer(l), Value::Integer(r)) = (&left_val, &right_val) {
                        Ok(Value::Boolean(l >= r))
                    } else {
                        Ok(Value::Boolean(
                            left_val.to_string() >= right_val.to_string(),
                        ))
                    }
                }
                parser_types::Operator::And => {
                    Ok(Value::Boolean(left_val.to_bool() && right_val.to_bool()))
                }
                parser_types::Operator::Or => {
                    Ok(Value::Boolean(left_val.to_bool() || right_val.to_bool()))
                }
            }
        }
        parser_types::Expr::Call(func_name, args) => {
            let mut values = Vec::new();
            for arg in args {
                values.push(eval_expr(arg, ctx)?);
            }
            call_dispatch(func_name, &values)
        }
        parser_types::Expr::Not(expr) => {
            let inner_value = eval_expr(*expr, ctx)?;
            Ok(Value::Boolean(!inner_value.to_bool()))
        }
        parser_types::Expr::Interpolated(elements) => {
            // Evaluate each element and concatenate the results
            // This handles compound expressions like: prefix$(VAR)suffix
            let mut result = String::new();
            for element in elements {
                match element {
                    parser_types::Element::Text(text) => result.push_str(text),
                    parser_types::Element::Html(html) => result.push_str(html),
                    parser_types::Element::Expr(expr) => {
                        let value = eval_expr(expr, ctx)?;
                        result.push_str(&value.to_string());
                    }
                    parser_types::Element::Esi(_) => {
                        // ESI tags in interpolated expressions should not happen
                        // but if they do, ignore them
                    }
                }
            }
            Ok(Value::Text(Cow::Owned(result)))
        }
    }
}

/// Evaluates an ESI expression string in the given context
///
/// # Arguments
/// * `raw_expr` - The raw expression string to evaluate
pub struct EvalContext {
    vars: HashMap<String, Value>,
    match_name: String,
    request: Request,
}
impl Default for EvalContext {
    fn default() -> Self {
        Self {
            vars: HashMap::new(),
            match_name: "MATCHES".to_string(),
            request: Request::new(Method::GET, "http://localhost"),
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
        }
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
            "QUERY_STRING" => self.request.get_query_str().map_or(Value::Null, |query| {
                debug!("Query string: {query}");
                subkey.map_or_else(
                    || Value::Text(Cow::Owned(query.to_string())),
                    |field| {
                        self.request
                            .get_query_parameter(field)
                            .map_or(Value::Null, |v| Value::Text(Cow::Owned(v.to_string())))
                    },
                )
            }),
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

            _ => self
                .vars
                .get(&format_key(key, subkey))
                .unwrap_or(&Value::Null)
                .to_owned(),
        }
    }
    pub fn set_variable(&mut self, key: &str, subkey: Option<&str>, value: Value) {
        let key = format_key(key, subkey);

        match value {
            Value::Null => {}
            _ => {
                self.vars.insert(key, value);
            }
        }
    }

    pub fn set_match_name(&mut self, match_name: &str) {
        self.match_name = match_name.to_string();
    }

    pub fn set_request(&mut self, request: Request) {
        self.request = request;
    }
}

impl<const N: usize> From<[(String, Value); N]> for EvalContext {
    fn from(data: [(String, Value); N]) -> Self {
        Self::new_with_vars(HashMap::from(data))
    }
}

fn format_key(key: &str, subkey: Option<&str>) -> String {
    subkey.map_or_else(|| key.to_string(), |subkey| format!("{key}[{subkey}]"))
}
/// Represents a value in an ESI expression.
///
/// Values can be of different types:
/// - `Integer`: A 32-bit signed integer
/// - `String`: A UTF-8 string
/// - `Boolean`: A boolean value (true/false)
/// - `Null`: Represents an absence of value
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Integer(i32),
    Text(Cow<'static, str>),
    Boolean(bool),
    Null,
}

impl Value {
    pub(crate) fn to_bool(&self) -> bool {
        match self {
            &Self::Integer(n) => !matches!(n, 0),
            Self::Text(s) => !matches!(s, s if s == &String::new()),
            Self::Boolean(b) => *b,
            &Self::Null => false,
        }
    }
}

impl From<String> for Value {
    fn from(s: String) -> Self {
        Self::Text(Cow::Owned(s)) // Convert `String` to `Cow::Owned`
    }
}

impl From<&str> for Value {
    fn from(s: &str) -> Self {
        Self::Text(Cow::Owned(s.to_owned())) // Convert `&str` to owned String
    }
}

impl AsRef<str> for Value {
    fn as_ref(&self) -> &str {
        match *self {
            Self::Text(ref text) => text.as_ref(),
            _ => panic!("Value is not a Text variant"),
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Integer(i) => write!(f, "{i}"),
            Self::Text(s) => write!(f, "{s}"),
            Self::Boolean(b) => write!(
                f,
                "{}",
                match b {
                    true => "true",
                    false => "false",
                }
            ),
            Self::Null => write!(f, "null"),
        }
    }
}

fn call_dispatch(identifier: &str, args: &[Value]) -> Result<Value> {
    match identifier {
        "ping" => Ok(Value::Text("pong".into())),
        "lower" => functions::lower(args),
        "html_encode" => functions::html_encode(args),
        "replace" => functions::replace(args),
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
        eval_expr(expr, ctx).map_err(|e| {
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
    fn test_eval_get_request_method() -> Result<()> {
        let mut ctx = EvalContext::new();
        let result = evaluate_expression("$(REQUEST_METHOD)", &mut ctx)?;
        assert_eq!(result, Value::Text("GET".into()));
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
        assert_eq!(result, Value::Text("hello".into()));
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
    fn test_string_coercion() -> Result<()> {
        assert_eq!(Value::Boolean(true).to_string(), "true");
        assert_eq!(Value::Boolean(false).to_string(), "false");
        assert_eq!(Value::Integer(1).to_string(), "1");
        assert_eq!(Value::Integer(0).to_string(), "0");
        assert_eq!(Value::Text("".into()).to_string(), "");
        assert_eq!(Value::Text("hello".into()).to_string(), "hello");
        assert_eq!(Value::Null.to_string(), "null");

        Ok(())
    }
    #[test]
    fn test_get_variable_query_string() {
        let mut ctx = EvalContext::new();
        let req = Request::new(Method::GET, "http://localhost?param=value");
        ctx.set_request(req);

        // Test without subkey
        let result = ctx.get_variable("QUERY_STRING", None);
        assert_eq!(result, Value::Text("param=value".into()));

        // Test with subkey
        let result = ctx.get_variable("QUERY_STRING", Some("param"));
        assert_eq!(result, Value::Text("value".into()));

        // Test with non-existent subkey
        let result = ctx.get_variable("QUERY_STRING", Some("nonexistent"));
        assert_eq!(result, Value::Null);
    }
}
