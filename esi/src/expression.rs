use fastly::http::Method;
use fastly::Request;
use regex::RegexBuilder;
use std::fmt::Write;
use std::iter::Peekable;
use std::slice::Iter;
use std::str::Chars;
use std::{collections::HashMap, fmt::Display};

use crate::{functions, ExecutionError, Result};

pub fn try_evaluate_interpolated(
    cur: &mut Peekable<Chars>,
    ctx: &mut EvalContext,
) -> Option<Value> {
    evaluate_interpolated(cur, ctx)
        .map_err(|e| {
            println!("Error while evaluating interpolated expression: {e}");
        })
        .ok()
}

pub fn evaluate_interpolated(cur: &mut Peekable<Chars>, ctx: &mut EvalContext) -> Result<Value> {
    let tokens = lex_interpolated_expr(cur)?;
    let expr = parse(&tokens)?;
    eval_expr(expr, ctx)
}

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
    pub fn get_variable(&self, key: &str, subkey: Option<String>) -> Value {
        match key {
            "REQUEST_METHOD" => Value::String(self.request.get_method_str().to_string()),
            "REQUEST_PATH" => Value::String(self.request.get_path().to_string()),
            "REMOTE_ADDR" => Value::String(
                self.request
                    .get_client_ip_addr()
                    .map_or_else(String::new, |ip| ip.to_string()),
            ),
            "QUERY_STRING" => match self.request.get_query_str() {
                Some(query) => match subkey {
                    None => Value::String(query.to_string()),
                    Some(field) => {
                        return self
                            .request
                            .get_query_parameter(&field)
                            .map_or_else(|| Value::Null, |v| Value::String(v.to_string()));
                    }
                },
                None => Value::Null,
            },
            _ if key.starts_with("HTTP_") => {
                let header = key.strip_prefix("HTTP_").unwrap_or_default();
                self.request.get_header(header).map_or(Value::Null, |h| {
                    let value = h.to_str().unwrap_or_default();
                    subkey.map_or_else(
                        || Value::String(value.to_string()),
                        |field| {
                            value
                                .split(';')
                                .find_map(|s| {
                                    s.trim()
                                        .split_once('=')
                                        .filter(|(key, _)| *key == field)
                                        .map(|(_, val)| Value::String(val.to_string()))
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
    pub fn set_variable(&mut self, key: &str, subkey: Option<String>, value: Value) {
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

fn format_key(key: &str, subkey: Option<String>) -> String {
    subkey.map_or_else(|| key.to_string(), |subkey| format!("{key}[{subkey}]"))
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Integer(i32),
    String(String),
    Boolean(BoolValue),
    Null,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoolValue {
    True,
    False,
}

impl Value {
    pub fn to_bool(&self) -> bool {
        match self {
            &Self::Integer(n) => !matches!(n, 0),
            Self::String(s) => !matches!(s, s if s == &String::new()),
            Self::Boolean(b) => *b == BoolValue::True,
            &Self::Null => false,
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Integer(i) => write!(f, "{i}"),
            Self::String(s) => write!(f, "{s}"),
            Self::Boolean(b) => write!(
                f,
                "{}",
                match b {
                    BoolValue::True => "true",
                    BoolValue::False => "false",
                }
            ),
            Self::Null => write!(f, "null"),
        }
    }
}

fn eval_expr(expr: Expr, ctx: &mut EvalContext) -> Result<Value> {
    let result = match expr {
        Expr::Integer(i) => Value::Integer(i),
        Expr::String(s) => Value::String(s),
        Expr::Variable(key, None) => ctx.get_variable(&key, None),
        Expr::Variable(key, Some(subkey_expr)) => {
            let subkey = eval_expr(*subkey_expr, ctx)?.to_string();
            ctx.get_variable(&key, Some(subkey))
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
                            let capval =
                                cap.map_or(Value::Null, |s| Value::String(s.as_str().to_string()));
                            ctx.set_variable(&ctx.match_name.clone(), Some(i.to_string()), capval);
                        }

                        Value::Boolean(BoolValue::True)
                    } else {
                        Value::Boolean(BoolValue::False)
                    }
                }
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
    Ok(result)
}

fn call_dispatch(identifier: &str, args: &[Value]) -> Result<Value> {
    match identifier {
        "ping" => Ok(Value::String("pong".to_string())),
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
    let node = if let Some(token) = cur.next() {
        match token {
            Token::Integer(i) => Expr::Integer(*i),
            Token::String(s) => Expr::String(s.clone()),
            Token::Dollar => parse_dollar(cur)?,
            unexpected => {
                return Err(ExecutionError::ExpressionError(format!(
                    "unexpected token starting expression: {unexpected:?}",
                )))
            }
        }
    } else {
        return Err(ExecutionError::ExpressionError(
            "unexpected end of tokens".to_string(),
        ));
    };

    // Check if there's a binary operation, or if we've reached the end of the expression
    match cur.peek() {
        Some(Token::Bareword(s)) => {
            let left = node;
            let operator = match s.as_str() {
                "matches" => {
                    cur.next();
                    Operator::Matches
                }
                "matches_i" => {
                    cur.next();
                    Operator::MatchesInsensitive
                }
                unexpected => {
                    return Err(ExecutionError::ExpressionError(format!(
                        "unexpected operator: {unexpected}"
                    )))
                }
            };
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
        Some(&Token::OpenParen) => parse_variable(cur),
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
        Some(&Token::OpenBracket) => {
            // TODO: I think there might be cases of $var{key} where key is a
            //       bareword. If that's the case, then handle here by checking
            //       if the next token is a bareword instead of trying to parse
            //       an expression.
            let subfield = parse_expr(cur)?;
            let Some(&Token::CloseBracket) = cur.next() else {
                return Err(ExecutionError::ExpressionError(format!(
                    "unexpected token: {:?}",
                    cur.next()
                )));
            };

            let Some(&Token::CloseParen) = cur.next() else {
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
        Some(&Token::CloseParen) => Ok(Expr::Variable(basename.to_string(), None)),
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
                result.push(get_bareword(cur));
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
            ' ' => {
                cur.next(); // Ignore spaces
            }
            _ => {
                return Err(ExecutionError::ExpressionError(
                    "error in lexing interpolated".to_string(),
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
        assert_eq!(tokens, vec![Token::Bareword("matches".to_string())]);
        Ok(())
    }
    #[test]
    fn test_lex_matches_i_operator() -> Result<()> {
        let tokens = lex_expr("matches_i")?;
        assert_eq!(tokens, vec![Token::Bareword("matches_i".to_string())]);
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
                Token::Bareword("matches".to_string()),
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
                right: Expr::String("bar".to_string())
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
        assert_eq!(result, Value::String("hello".to_string()));
        Ok(())
    }

    #[test]
    fn test_eval_variable() -> Result<()> {
        let expr = Expr::Variable("hello".to_string(), None);
        let result = eval_expr(
            expr,
            &mut EvalContext::from([("hello".to_string(), Value::String("goodbye".to_string()))]),
        )?;
        assert_eq!(result, Value::String("goodbye".to_string()));
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
            &mut EvalContext::from([(
                "hello[abc]".to_string(),
                Value::String("goodbye".to_string()),
            )]),
        )?;
        assert_eq!(result, Value::String("goodbye".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_matches_comparison() -> Result<()> {
        let result = evaluate_expression(
            "$(hello) matches '^foo'",
            &mut EvalContext::from([("hello".to_string(), Value::String("foobar".to_string()))]),
        )?;
        assert_eq!(result, Value::Boolean(BoolValue::True));
        Ok(())
    }
    #[test]
    fn test_eval_matches_i_comparison() -> Result<()> {
        let result = evaluate_expression(
            "$(hello) matches_i '^foo'",
            &mut EvalContext::from([("hello".to_string(), Value::String("FOOBAR".to_string()))]),
        )?;
        assert_eq!(result, Value::Boolean(BoolValue::True));
        Ok(())
    }
    #[test]
    fn test_eval_matches_with_captures() -> Result<()> {
        let mut ctx =
            &mut EvalContext::from([("hello".to_string(), Value::String("foobar".to_string()))]);

        let result = evaluate_expression("$(hello) matches '^(fo)o'", &mut ctx)?;
        assert_eq!(result, Value::Boolean(BoolValue::True));

        let result = evaluate_expression("$(MATCHES{1})", &mut ctx)?;
        assert_eq!(result, Value::String("fo".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_matches_with_captures_and_match_name() -> Result<()> {
        let mut ctx =
            &mut EvalContext::from([("hello".to_string(), Value::String("foobar".to_string()))]);

        ctx.set_match_name("my_custom_name");
        let result = evaluate_expression("$(hello) matches '^(fo)o'", ctx)?;
        assert_eq!(result, Value::Boolean(BoolValue::True));

        let result = evaluate_expression("$(my_custom_name{1})", &mut ctx)?;
        assert_eq!(result, Value::String("fo".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_matches_comparison_negative() -> Result<()> {
        let result = evaluate_expression(
            "$(hello) matches '^foo'",
            &mut EvalContext::from([("hello".to_string(), Value::String("nope".to_string()))]),
        )?;
        assert_eq!(result, Value::Boolean(BoolValue::False));
        Ok(())
    }
    #[test]
    fn test_eval_function_call() -> Result<()> {
        let result = evaluate_expression("$ping()", &mut EvalContext::new())?;
        assert_eq!(result, Value::String("pong".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_lower_call() -> Result<()> {
        let result = evaluate_expression("$lower('FOO')", &mut EvalContext::new())?;
        assert_eq!(result, Value::String("foo".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_html_encode_call() -> Result<()> {
        let result = evaluate_expression("$html_encode('a > b < c')", &mut EvalContext::new())?;
        assert_eq!(result, Value::String("a &gt; b &lt; c".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_replace_call() -> Result<()> {
        let result = evaluate_expression(
            "$replace('abc-def-ghi-', '-', '==')",
            &mut EvalContext::new(),
        )?;
        assert_eq!(result, Value::String("abc==def==ghi==".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_replace_call_with_empty_string() -> Result<()> {
        let result =
            evaluate_expression("$replace('abc-def-ghi-', '-', '')", &mut EvalContext::new())?;
        assert_eq!(result, Value::String("abcdefghi".to_string()));
        Ok(())
    }

    #[test]
    fn test_eval_replace_call_with_count() -> Result<()> {
        let result = evaluate_expression(
            "$replace('abc-def-ghi-', '-', '==', 2)",
            &mut EvalContext::new(),
        )?;
        assert_eq!(result, Value::String("abc==def==ghi-".to_string()));
        Ok(())
    }

    #[test]
    fn test_eval_get_request_method() -> Result<()> {
        let mut ctx = EvalContext::new();
        let result = evaluate_expression("$(REQUEST_METHOD)", &mut ctx)?;
        assert_eq!(result, Value::String("GET".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_get_request_path() -> Result<()> {
        let mut ctx = EvalContext::new();
        ctx.set_request(Request::new(Method::GET, "http://localhost/hello/there"));

        let result = evaluate_expression("$(REQUEST_PATH)", &mut ctx)?;
        assert_eq!(result, Value::String("/hello/there".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_get_request_query() -> Result<()> {
        let mut ctx = EvalContext::new();
        ctx.set_request(Request::new(Method::GET, "http://localhost?hello"));

        let result = evaluate_expression("$(QUERY_STRING)", &mut ctx)?;
        assert_eq!(result, Value::String("hello".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_get_request_query_field() -> Result<()> {
        let mut ctx = EvalContext::new();
        ctx.set_request(Request::new(Method::GET, "http://localhost?hello=goodbye"));

        let result = evaluate_expression("$(QUERY_STRING{'hello'})", &mut ctx)?;
        assert_eq!(result, Value::String("goodbye".to_string()));
        let result = evaluate_expression("$(QUERY_STRING{'nonexistent'})", &mut ctx)?;
        assert_eq!(result, Value::Null);
        Ok(())
    }
    #[test]
    fn test_eval_get_remote_addr() -> Result<()> {
        // This is kind of a useless test as this will always return an empty string.
        let mut ctx = EvalContext::new();
        ctx.set_request(Request::new(Method::GET, "http://localhost?hello"));

        let result = evaluate_expression("$(REMOTE_ADDR)", &mut ctx)?;
        assert_eq!(result, Value::String("".to_string()));
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
        assert_eq!(result, Value::String("hello.com".to_string()));
        let result = evaluate_expression("$(HTTP_FOOBAR)", &mut ctx)?;
        assert_eq!(result, Value::String("baz".to_string()));
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
        assert_eq!(result, Value::String("bar".to_string()));
        let result = evaluate_expression("$(HTTP_COOKIE{'bar'})", &mut ctx)?;
        assert_eq!(result, Value::String("baz".to_string()));
        let result = evaluate_expression("$(HTTP_COOKIE{'baz'})", &mut ctx)?;
        assert_eq!(result, Value::Null);
        Ok(())
    }

    #[test]
    fn test_bool_coercion() -> Result<()> {
        assert_eq!(Value::Boolean(BoolValue::True).to_bool(), true);
        assert_eq!(Value::Boolean(BoolValue::False).to_bool(), false);
        assert_eq!(Value::Integer(1).to_bool(), true);
        assert_eq!(Value::Integer(0).to_bool(), false);
        assert_eq!(Value::String("".to_string()).to_bool(), false);
        assert_eq!(Value::String("hello".to_string()).to_bool(), true);
        assert_eq!(Value::Null.to_bool(), false);

        Ok(())
    }

    #[test]
    fn test_string_coercion() -> Result<()> {
        assert_eq!(Value::Boolean(BoolValue::True).to_string(), "true");
        assert_eq!(Value::Boolean(BoolValue::False).to_string(), "false");
        assert_eq!(Value::Integer(1).to_string(), "1");
        assert_eq!(Value::Integer(0).to_string(), "0");
        assert_eq!(Value::String("".to_string()).to_string(), "");
        assert_eq!(Value::String("hello".to_string()).to_string(), "hello");
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
}
