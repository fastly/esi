use fastly::http::Method;
use fastly::Request;
use log::debug;
use regex::RegexBuilder;
use std::borrow::Cow;
use std::fmt::Write;
use std::iter::Peekable;
use std::slice::Iter;
use std::str::Chars;
use std::{collections::HashMap, fmt::Display};

use crate::{functions, ExecutionError, Result};
/// Attempts to evaluate an interpolated expression, returning None on failure
///
/// This function evaluates expressions like `$(HTTP_HOST)` in ESI markup, gracefully
/// handling failures by returning None instead of propagating errors. This ensures
/// that a failed expression evaluation does not halt overall document processing.
///
/// # Arguments
/// * `cur` - Peekable character iterator containing the expression to evaluate
/// * `ctx` - Evaluation context containing variables and state
///
/// # Returns
/// * `Option<Value>` - The evaluated expression value if successful, None if evaluation fails
/// ```
pub fn try_evaluate_interpolated(
    cur: &mut Peekable<Chars>,
    ctx: &mut EvalContext,
) -> Option<Value> {
    evaluate_interpolated(cur, ctx)
        .map_err(|e| {
            // We eat the error here because a failed expression should result in an empty result
            // and not prevent the rest of the file from processing.
            debug!("Error while evaluating interpolated expression: {e}");
        })
        .ok()
}

fn evaluate_interpolated(cur: &mut Peekable<Chars>, ctx: &mut EvalContext) -> Result<Value> {
    lex_interpolated_expr(cur)
        .and_then(|tokens| parse(&tokens))
        .and_then(|expr| eval_expr(expr, ctx))
}

/// Evaluates an ESI expression string in the given context
///
/// # Arguments
/// * `raw_expr` - The raw expression string to evaluate
/// * `ctx` - Evaluation context containing variables and state
///
/// # Returns
/// * `Result<Value>` - The evaluated expression result or an error
///
pub fn evaluate_expression(raw_expr: &str, ctx: &mut EvalContext) -> Result<Value> {
    lex_expr(raw_expr)
        .and_then(|tokens| parse(&tokens))
        .and_then(|expr: Expr| eval_expr(expr, ctx))
        .map_err(|e| {
            ExecutionError::ExpressionError(format!(
                "Error occurred during expression evaluation: {e}"
            ))
        })
}

pub struct EvalContext {
    vars: HashMap<String, Value>,
    match_name: String,
    request: Request,
}
impl EvalContext {
    pub fn new() -> Self {
        Self {
            vars: HashMap::new(),
            match_name: "MATCHES".to_string(),
            request: Request::new(Method::GET, "http://localhost"),
        }
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
        };
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

fn eval_expr(expr: Expr, ctx: &mut EvalContext) -> Result<Value> {
    let result = match expr {
        Expr::Integer(i) => Value::Integer(i),
        Expr::String(s) => Value::Text(s.into()),
        Expr::Variable(key, None) => ctx.get_variable(&key, None),
        Expr::Variable(key, Some(subkey_expr)) => {
            let subkey = eval_expr(*subkey_expr, ctx)?.to_string();
            ctx.get_variable(&key, Some(&subkey))
        }
        Expr::Comparison(c) => {
            let left = eval_expr(c.left, ctx)?;
            let right = eval_expr(c.right, ctx)?;
            match c.operator {
                Operator::Matches | Operator::MatchesInsensitive => {
                    let test = left.to_string();
                    let pattern = right.to_string();

                    let re = if c.operator == Operator::Matches {
                        RegexBuilder::new(&pattern).build()?
                    } else {
                        RegexBuilder::new(&pattern).case_insensitive(true).build()?
                    };

                    if let Some(captures) = re.captures(&test) {
                        for (i, cap) in captures.iter().enumerate() {
                            let capval = cap.map_or(Value::Null, |s| {
                                Value::Text(Cow::Owned(s.as_str().into()))
                            });
                            {
                                ctx.set_variable(
                                    &ctx.match_name.clone(),
                                    Some(&i.to_string()),
                                    capval,
                                );
                            }
                        }
                        Value::Boolean(true)
                    } else {
                        Value::Boolean(false)
                    }
                }
                Operator::Equals => Value::Boolean(left.to_string() == right.to_string()),
                Operator::NotEquals => Value::Boolean(left.to_string() != right.to_string()),
            }
        }
        Expr::Call(identifier, args) => {
            let mut values = Vec::new();
            for arg in args {
                values.push(eval_expr(arg, ctx)?);
            }
            call_dispatch(&identifier, &values)?
        }
    };
    debug!("Expression result: {:?}", result);
    Ok(result)
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

#[derive(Debug, Clone, PartialEq)]
enum Expr {
    Integer(i32),
    String(String),
    Variable(String, Option<Box<Expr>>),
    Comparison(Box<Comparison>),
    Call(String, Vec<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
enum Operator {
    Matches,
    MatchesInsensitive,
    Equals,
    NotEquals,
}

#[derive(Debug, Clone, PartialEq)]
struct Comparison {
    left: Expr,
    operator: Operator,
    right: Expr,
}
// The parser attempts to implement this BNF:
//
// Expr     <- integer | string | Variable | Call | BinaryOp
// Variable <- '$' '(' bareword ['{' Expr '}'] ')'
// Call     <- '$' bareword '(' Expr? [',' Expr] ')'
// BinaryOp <- Expr Operator Expr
//
fn parse(tokens: &[Token]) -> Result<Expr> {
    let mut cur = tokens.iter().peekable();

    let expr = parse_expr(&mut cur)
        .map_err(|e| ExecutionError::ExpressionError(format!("parse error: {e}")))?;

    // Check if we've reached the end of the tokens
    if cur.peek().is_some() {
        let cur_left = cur.fold(String::new(), |mut acc, t| {
            write!(&mut acc, "{t:?}").unwrap();
            acc
        });
        return Err(ExecutionError::ExpressionError(format!(
            "expected eof. tokens left: {cur_left}"
        )));
    }

    Ok(expr)
}

fn parse_expr(cur: &mut Peekable<Iter<Token>>) -> Result<Expr> {
    println!("Parsing expression, current token: {:?}", cur);
    let node = if let Some(token) = cur.next() {
        match token {
            Token::Integer(i) => Expr::Integer(*i),
            Token::String(s) => Expr::String(s.clone()),
            Token::Dollar => parse_dollar(cur)?,
            unexpected => {
                return Err(ExecutionError::ExpressionError(format!(
                    "unexpected token starting expression: {unexpected:?}",
                )));
            }
        }
    } else {
        return Err(ExecutionError::ExpressionError(
            "unexpected end of tokens".to_string(),
        ));
    };

    // Check if there's a binary operation, or if we've reached the end of the expression
    match cur.peek() {
        Some(Token::Operation(op)) => {
            let operator = op.clone();
            cur.next(); // consume the operator token
            let left = node;
            let right = parse_expr(cur)?;
            let expr = Expr::Comparison(Box::new(Comparison {
                left,
                operator,
                right,
            }));
            Ok(expr)
        }
        _ => Ok(node),
    }
}

fn parse_dollar(cur: &mut Peekable<Iter<Token>>) -> Result<Expr> {
    match cur.next() {
        Some(Token::OpenParen) => parse_variable(cur),
        Some(Token::Bareword(s)) => parse_call(s, cur),
        unexpected => Err(ExecutionError::ExpressionError(format!(
            "unexpected token: {unexpected:?}",
        ))),
    }
}

fn parse_variable(cur: &mut Peekable<Iter<Token>>) -> Result<Expr> {
    let Some(Token::Bareword(basename)) = cur.next() else {
        return Err(ExecutionError::ExpressionError(format!(
            "unexpected token: {:?}",
            cur.next()
        )));
    };

    match cur.next() {
        Some(Token::OpenBracket) => {
            // Allow bareword as string in subfield position
            let subfield = if let Some(Token::Bareword(s)) = cur.peek() {
                debug!("Parsing bareword subfield: {s}");
                cur.next();
                Expr::String(s.clone())
            } else {
                debug!("Parsing non-bareword subfield, {:?}", cur.peek());
                // Parse the subfield expression
                parse_expr(cur)?
            };

            let Some(Token::CloseBracket) = cur.next() else {
                return Err(ExecutionError::ExpressionError(format!(
                    "unexpected token: {:?}",
                    cur.next()
                )));
            };

            let Some(Token::CloseParen) = cur.next() else {
                return Err(ExecutionError::ExpressionError(format!(
                    "unexpected token: {:?}",
                    cur.next()
                )));
            };

            Ok(Expr::Variable(
                basename.to_string(),
                Some(Box::new(subfield)),
            ))
        }
        Some(Token::CloseParen) => Ok(Expr::Variable(basename.to_string(), None)),
        unexpected => Err(ExecutionError::ExpressionError(format!(
            "unexpected token: {unexpected:?}",
        ))),
    }
}

fn parse_call(identifier: &str, cur: &mut Peekable<Iter<Token>>) -> Result<Expr> {
    match cur.next() {
        Some(Token::OpenParen) => {
            let mut args = Vec::new();
            loop {
                if Some(&&Token::CloseParen) == cur.peek() {
                    cur.next();
                    break;
                }
                args.push(parse_expr(cur)?);
                match cur.peek() {
                    Some(&&Token::CloseParen) => {
                        cur.next();
                        break;
                    }
                    Some(&&Token::Comma) => {
                        cur.next();
                        continue;
                    }
                    _ => {
                        return Err(ExecutionError::ExpressionError(
                            "unexpected token in arg list".to_string(),
                        ));
                    }
                }
            }
            Ok(Expr::Call(identifier.to_string(), args))
        }
        _ => Err(ExecutionError::ExpressionError(
            "unexpected token following identifier".to_string(),
        )),
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Token {
    Integer(i32),
    String(String),
    OpenParen,
    CloseParen,
    OpenBracket,
    CloseBracket,
    Comma,
    Dollar,
    Operation(Operator),
    Negation,
    Bareword(String),
}

fn lex_expr(expr: &str) -> Result<Vec<Token>> {
    let mut cur = expr.chars().peekable();
    // Lex the expression, but don't stop at the first closing paren
    let single = false;
    lex_tokens(&mut cur, single)
}

fn lex_interpolated_expr(cur: &mut Peekable<Chars>) -> Result<Vec<Token>> {
    if cur.peek() != Some(&'$') {
        return Err(ExecutionError::ExpressionError("no expression".to_string()));
    }
    // Lex the expression, but stop at the first closing paren
    let single = true;
    lex_tokens(cur, single)
}

// Lexes an expression, stopping at the first closing paren if `single` is true
fn lex_tokens(cur: &mut Peekable<Chars>, single: bool) -> Result<Vec<Token>> {
    let mut result = Vec::new();
    let mut paren_depth = 0;

    while let Some(&c) = cur.peek() {
        match c {
            '\'' => {
                cur.next();
                result.push(get_string(cur)?);
            }
            '$' => {
                cur.next();
                result.push(Token::Dollar);
            }
            '0'..='9' | '-' => {
                result.push(get_integer(cur)?);
            }
            'a'..='z' | 'A'..='Z' => {
                let bareword = get_bareword(cur);

                // Check if it's an operator
                if let Token::Bareword(ref word) = bareword {
                    match word.as_str() {
                        "matches" => result.push(Token::Operation(Operator::Matches)),
                        "matches_i" => result.push(Token::Operation(Operator::MatchesInsensitive)),
                        _ => result.push(bareword),
                    }
                } else {
                    result.push(get_bareword(cur));
                }
            }
            '(' | ')' | '{' | '}' | ',' => {
                cur.next();
                match c {
                    '(' => {
                        result.push(Token::OpenParen);
                        paren_depth += 1;
                    }
                    ')' => {
                        result.push(Token::CloseParen);
                        paren_depth -= 1;
                        if single && paren_depth <= 0 {
                            break;
                        }
                    }
                    '{' => result.push(Token::OpenBracket),
                    '}' => result.push(Token::CloseBracket),
                    ',' => result.push(Token::Comma),
                    _ => unreachable!(),
                }
            }
            '=' => {
                cur.next(); // consume the first '='
                if cur.peek() == Some(&'=') {
                    cur.next(); // consume the second '='
                    result.push(Token::Operation(Operator::Equals));
                } else {
                    return Err(ExecutionError::ExpressionError(
                        "single '=' not supported, use '==' for equality".to_string(),
                    ));
                }
            }
            '!' => {
                cur.next(); // consume first '!'
                if cur.peek() == Some(&'=') {
                    cur.next(); // consume the '='
                    result.push(Token::Operation(Operator::NotEquals));
                } else if cur.peek() == Some(&'$') || cur.peek() == Some(&'(') {
                    result.push(Token::Negation);
                }
            }
            ' ' => {
                cur.next(); // Ignore spaces
            }
            _ => {
                return Err(ExecutionError::ExpressionError(
                    // "error in lexing interpolated".to_string(),
                    format!("error in lexing interpolated `{c}`"),
                ));
            }
        }
    }
    // We should have hit the end of the expression
    if paren_depth != 0 {
        return Err(ExecutionError::ExpressionError(
            "missing closing parenthesis".to_string(),
        ));
    }

    Ok(result)
}

fn get_integer(cur: &mut Peekable<Chars>) -> Result<Token> {
    let mut buf = Vec::new();
    let c = cur.next().unwrap();
    buf.push(c);

    if c == '0' {
        // Zero is a special case, as the only number that can start with a zero.
        let Some(c) = cur.peek() else {
            cur.next();
            // EOF after a zero. That's a valid number.
            return Ok(Token::Integer(0));
        };
        // Make sure the zero isn't followed by another digit.
        if let '0'..='9' = *c {
            return Err(ExecutionError::ExpressionError(
                "invalid number".to_string(),
            ));
        }
    }

    if c == '-' {
        let Some(c) = cur.next() else {
            return Err(ExecutionError::ExpressionError(
                "invalid number".to_string(),
            ));
        };
        match c {
            '1'..='9' => buf.push(c),
            _ => {
                return Err(ExecutionError::ExpressionError(
                    "invalid number".to_string(),
                ))
            }
        }
    }

    while let Some(c) = cur.peek() {
        match c {
            '0'..='9' => buf.push(cur.next().unwrap()),
            _ => break,
        }
    }
    let Ok(num) = buf.into_iter().collect::<String>().parse() else {
        return Err(ExecutionError::ExpressionError(
            "invalid number".to_string(),
        ));
    };
    Ok(Token::Integer(num))
}

fn get_bareword(cur: &mut Peekable<Chars>) -> Token {
    let mut buf = Vec::new();
    buf.push(cur.next().unwrap());

    while let Some(c) = cur.peek() {
        match c {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '_' => buf.push(cur.next().unwrap()),
            _ => break,
        }
    }
    Token::Bareword(buf.into_iter().collect())
}

fn get_string(cur: &mut Peekable<Chars>) -> Result<Token> {
    let mut buf = Vec::new();
    let mut triple_tick = false;

    if cur.peek() == Some(&'\'') {
        // This is either an empty string, or the start of a triple tick string
        cur.next();
        if cur.peek() == Some(&'\'') {
            // It's a triple tick string
            triple_tick = true;
            cur.next();
        } else {
            // It's an empty string, let's just return it
            return Ok(Token::String(String::new()));
        }
    }

    while let Some(c) = cur.next() {
        match c {
            '\'' => {
                if !triple_tick {
                    break;
                }
                if let Some(c2) = cur.next() {
                    if c2 == '\'' && cur.peek() == Some(&'\'') {
                        // End of a triple tick string
                        cur.next();
                        break;
                    }
                    // Just two ticks
                    buf.push(c);
                    buf.push(c2);
                } else {
                    // error
                    return Err(ExecutionError::ExpressionError(
                        "unexpected eof while parsing string".to_string(),
                    ));
                };
            }
            '\\' => {
                if triple_tick {
                    // no escaping inside a triple tick string
                    buf.push(c);
                } else {
                    // in a normal string, we'll ignore this and buffer the
                    // next char
                    if let Some(escaped_c) = cur.next() {
                        buf.push(escaped_c);
                    } else {
                        // error
                        return Err(ExecutionError::ExpressionError(
                            "unexpected eof while parsing string".to_string(),
                        ));
                    }
                }
            }
            _ => buf.push(c),
        }
    }
    Ok(Token::String(buf.into_iter().collect()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use regex::Regex;

    #[test]
    fn test_lex_integer() -> Result<()> {
        let tokens = lex_expr("1 23 456789 0 -987654 -32 -1 0")?;
        assert_eq!(
            tokens,
            vec![
                Token::Integer(1),
                Token::Integer(23),
                Token::Integer(456789),
                Token::Integer(0),
                Token::Integer(-987654),
                Token::Integer(-32),
                Token::Integer(-1),
                Token::Integer(0)
            ]
        );
        Ok(())
    }
    #[test]
    fn test_lex_empty_string() -> Result<()> {
        let tokens = lex_expr("''")?;
        assert_eq!(tokens, vec![Token::String("".to_string())]);
        Ok(())
    }
    #[test]
    fn test_lex_simple_string() -> Result<()> {
        let tokens = lex_expr("'hello'")?;
        assert_eq!(tokens, vec![Token::String("hello".to_string())]);
        Ok(())
    }
    #[test]
    fn test_lex_escaped_string() -> Result<()> {
        let tokens = lex_expr(r#"'hel\'lo'"#)?;
        assert_eq!(tokens, vec![Token::String("hel\'lo".to_string())]);
        Ok(())
    }
    #[test]
    fn test_lex_triple_tick_string() -> Result<()> {
        let tokens = lex_expr(r#"'''h'el''l\'o\'''"#)?;
        assert_eq!(tokens, vec![Token::String(r#"h'el''l\'o\"#.to_string())]);
        Ok(())
    }
    #[test]
    fn test_lex_triple_tick_and_escaping_torture() -> Result<()> {
        let tokens = lex_expr(r#"'\\\'triple\'/' matches '''\'triple'/'''"#)?;
        assert_eq!(tokens[0], tokens[2]);
        let Token::String(ref test) = tokens[0] else {
            panic!()
        };
        let Token::String(ref pattern) = tokens[2] else {
            panic!()
        };
        let re = Regex::new(pattern)?;
        assert!(re.is_match(test));
        Ok(())
    }

    #[test]
    fn test_lex_variable() -> Result<()> {
        let tokens = lex_expr("$(hello)")?;
        assert_eq!(
            tokens,
            vec![
                Token::Dollar,
                Token::OpenParen,
                Token::Bareword("hello".to_string()),
                Token::CloseParen
            ]
        );
        Ok(())
    }
    #[test]
    fn test_lex_variable_with_subscript() -> Result<()> {
        let tokens = lex_expr("$(hello{'goodbye'})")?;
        assert_eq!(
            tokens,
            vec![
                Token::Dollar,
                Token::OpenParen,
                Token::Bareword("hello".to_string()),
                Token::OpenBracket,
                Token::String("goodbye".to_string()),
                Token::CloseBracket,
                Token::CloseParen,
            ]
        );
        Ok(())
    }
    #[test]
    fn test_lex_variable_with_integer_subscript() -> Result<()> {
        let tokens = lex_expr("$(hello{6})")?;
        assert_eq!(
            tokens,
            vec![
                Token::Dollar,
                Token::OpenParen,
                Token::Bareword("hello".to_string()),
                Token::OpenBracket,
                Token::Integer(6),
                Token::CloseBracket,
                Token::CloseParen,
            ]
        );
        Ok(())
    }
    #[test]
    fn test_lex_matches_operator() -> Result<()> {
        let tokens = lex_expr("matches")?;
        assert_eq!(tokens, vec![Token::Operation(Operator::Matches)]);
        Ok(())
    }
    #[test]
    fn test_lex_matches_i_operator() -> Result<()> {
        let tokens = lex_expr("matches_i")?;
        assert_eq!(tokens, vec![Token::Operation(Operator::MatchesInsensitive)]);
        Ok(())
    }
    #[test]
    fn test_lex_identifier() -> Result<()> {
        let tokens = lex_expr("$foo2BAZ")?;
        assert_eq!(
            tokens,
            vec![Token::Dollar, Token::Bareword("foo2BAZ".to_string())]
        );
        Ok(())
    }
    #[test]
    fn test_lex_simple_call() -> Result<()> {
        let tokens = lex_expr("$fn()")?;
        assert_eq!(
            tokens,
            vec![
                Token::Dollar,
                Token::Bareword("fn".to_string()),
                Token::OpenParen,
                Token::CloseParen
            ]
        );
        Ok(())
    }
    #[test]
    fn test_lex_call_with_arg() -> Result<()> {
        let tokens = lex_expr("$fn('hello')")?;
        assert_eq!(
            tokens,
            vec![
                Token::Dollar,
                Token::Bareword("fn".to_string()),
                Token::OpenParen,
                Token::String("hello".to_string()),
                Token::CloseParen
            ]
        );
        Ok(())
    }
    #[test]
    fn test_lex_call_with_empty_string_arg() -> Result<()> {
        let tokens = lex_expr("$fn('')")?;
        assert_eq!(
            tokens,
            vec![
                Token::Dollar,
                Token::Bareword("fn".to_string()),
                Token::OpenParen,
                Token::String("".to_string()),
                Token::CloseParen
            ]
        );
        Ok(())
    }
    #[test]
    fn test_lex_call_with_two_args() -> Result<()> {
        let tokens = lex_expr("$fn($(hello), 'hello')")?;
        assert_eq!(
            tokens,
            vec![
                Token::Dollar,
                Token::Bareword("fn".to_string()),
                Token::OpenParen,
                Token::Dollar,
                Token::OpenParen,
                Token::Bareword("hello".to_string()),
                Token::CloseParen,
                Token::Comma,
                Token::String("hello".to_string()),
                Token::CloseParen
            ]
        );
        Ok(())
    }
    #[test]
    fn test_lex_comparison() -> Result<()> {
        let tokens = lex_expr("$(foo) matches 'bar'")?;
        assert_eq!(
            tokens,
            vec![
                Token::Dollar,
                Token::OpenParen,
                Token::Bareword("foo".to_string()),
                Token::CloseParen,
                Token::Operation(Operator::Matches),
                Token::String("bar".to_string())
            ]
        );
        Ok(())
    }

    #[test]
    fn test_parse_integer() -> Result<()> {
        let tokens = lex_expr("1")?;
        let expr = parse(&tokens)?;
        assert_eq!(expr, Expr::Integer(1));
        Ok(())
    }
    #[test]
    fn test_parse_simple_string() -> Result<()> {
        let tokens = lex_expr("'hello'")?;
        let expr = parse(&tokens)?;
        assert_eq!(expr, Expr::String("hello".to_string()));
        Ok(())
    }
    #[test]
    fn test_parse_variable() -> Result<()> {
        let tokens = lex_expr("$(hello)")?;
        let expr = parse(&tokens)?;
        assert_eq!(expr, Expr::Variable("hello".to_string(), None));
        Ok(())
    }

    #[test]
    fn test_parse_comparison() -> Result<()> {
        let tokens = lex_expr("$(foo) matches 'bar'")?;
        let expr = parse(&tokens)?;
        assert_eq!(
            expr,
            Expr::Comparison(Box::new(Comparison {
                left: Expr::Variable("foo".to_string(), None),
                operator: Operator::Matches,
                right: Expr::String("bar".to_string()),
            }))
        );
        Ok(())
    }
    #[test]
    fn test_parse_call() -> Result<()> {
        let tokens = lex_expr("$hello()")?;
        let expr = parse(&tokens)?;
        assert_eq!(expr, Expr::Call("hello".to_string(), Vec::new()));
        Ok(())
    }
    #[test]
    fn test_parse_call_with_arg() -> Result<()> {
        let tokens = lex_expr("$fn('hello')")?;
        let expr = parse(&tokens)?;
        assert_eq!(
            expr,
            Expr::Call("fn".to_string(), vec![Expr::String("hello".to_string())])
        );
        Ok(())
    }
    #[test]
    fn test_parse_call_with_two_args() -> Result<()> {
        let tokens = lex_expr("$fn($(hello), 'hello')")?;
        let expr = parse(&tokens)?;
        assert_eq!(
            expr,
            Expr::Call(
                "fn".to_string(),
                vec![
                    Expr::Variable("hello".to_string(), None),
                    Expr::String("hello".to_string())
                ]
            )
        );
        Ok(())
    }

    #[test]
    fn test_eval_string() -> Result<()> {
        let expr = Expr::String("hello".to_string());
        let result = eval_expr(expr, &mut EvalContext::new())?;
        assert_eq!(result, Value::Text("hello".into()));
        Ok(())
    }

    #[test]
    fn test_eval_variable() -> Result<()> {
        let expr = Expr::Variable("hello".to_string(), None);
        let result = eval_expr(
            expr,
            &mut EvalContext::from([("hello".to_string(), Value::Text("goodbye".into()))]),
        )?;
        assert_eq!(result, Value::Text("goodbye".into()));
        Ok(())
    }
    #[test]
    fn test_eval_subscripted_variable() -> Result<()> {
        let expr = Expr::Variable(
            "hello".to_string(),
            Some(Box::new(Expr::String("abc".to_string()))),
        );
        let result = eval_expr(
            expr,
            &mut EvalContext::from([("hello[abc]".to_string(), Value::Text("goodbye".into()))]),
        )?;
        assert_eq!(result, Value::Text("goodbye".into()));
        Ok(())
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
    fn test_lex_interpolated_basic() -> Result<()> {
        let mut chars = "$(foo)bar".chars().peekable();
        let tokens = lex_interpolated_expr(&mut chars)?;
        assert_eq!(
            tokens,
            vec![
                Token::Dollar,
                Token::OpenParen,
                Token::Bareword("foo".to_string()),
                Token::CloseParen
            ]
        );
        // Verify remaining chars are untouched
        assert_eq!(chars.collect::<String>(), "bar");
        Ok(())
    }

    #[test]
    fn test_lex_interpolated_nested() -> Result<()> {
        let mut chars = "$(foo{$(bar)})rest".chars().peekable();
        let tokens = lex_interpolated_expr(&mut chars)?;
        assert_eq!(
            tokens,
            vec![
                Token::Dollar,
                Token::OpenParen,
                Token::Bareword("foo".to_string()),
                Token::OpenBracket,
                Token::Dollar,
                Token::OpenParen,
                Token::Bareword("bar".to_string()),
                Token::CloseParen,
                Token::CloseBracket,
                Token::CloseParen
            ]
        );
        assert_eq!(chars.collect::<String>(), "rest");
        Ok(())
    }

    #[test]
    fn test_lex_interpolated_no_dollar() {
        let mut chars = "foo".chars().peekable();
        assert!(lex_interpolated_expr(&mut chars).is_err());
    }

    #[test]
    fn test_lex_interpolated_incomplete() {
        let mut chars = "$(foo".chars().peekable();
        assert!(lex_interpolated_expr(&mut chars).is_err());
    }

    #[test]
    fn test_var_subfield_missing_closing_bracket() {
        let input = r#"
        <esi:vars>
            $(QUERY_STRING{param)
        </esi:vars>
        "#;
        let mut chars = input.chars().peekable();
        assert!(lex_interpolated_expr(&mut chars).is_err());
    }

    #[test]
    fn test_invalid_standalone_bareword() {
        let input = r#"
        <esi:vars>
            bareword
        </esi:vars>
        "#;
        let mut chars = input.chars().peekable();
        assert!(lex_interpolated_expr(&mut chars).is_err());
    }

    #[test]
    fn test_mixed_subfield_types() {
        let input = r#"$(QUERY_STRING{param})"#;
        let mut chars = input.chars().peekable();
        // let result =
        // evaluate_interpolated(&mut chars, &mut ctx).expect("Processing should succeed");
        let result = lex_interpolated_expr(&mut chars).expect("Processing should succeed");
        println!("Tokens: {:?}", result);
        assert_eq!(
            result,
            vec![
                Token::Dollar,
                Token::OpenParen,
                Token::Bareword("QUERY_STRING".into()),
                Token::OpenBracket,
                Token::Bareword("param".into()),
                Token::CloseBracket,
                Token::CloseParen
            ]
        );
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
