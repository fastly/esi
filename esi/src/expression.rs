use fastly::http::Method;
use fastly::Request;
use regex::RegexBuilder;
use std::collections::HashMap;
use std::iter::Peekable;
use std::slice::Iter;
use std::str::Chars;

use crate::{ExecutionError, Result};

pub fn evaluate_expression(raw_expr: String, ctx: &mut EvalContext) -> Result<Value> {
    // TODO: this got real ugly, figure out some better way to do this
    let tokens = match lex_expr(raw_expr) {
        Ok(r) => r,
        Err(ExecutionError::ExpressionParseError(s)) => return Ok(Value::Error(s)),
        Err(e) => return Err(e),
    };
    let expr = match parse(tokens) {
        Ok(r) => r,
        Err(ExecutionError::ExpressionParseError(s)) => return Ok(Value::Error(s)),
        Err(e) => return Err(e),
    };
    match eval_expr(expr, ctx) {
        Ok(r) => Ok(r),
        Err(ExecutionError::ExpressionParseError(s)) => return Ok(Value::Error(s)),
        Err(e) => return Err(e),
    }
}

pub struct EvalContext {
    vars: HashMap<String, Value>,
    match_name: String,
    request: Request,
}
impl EvalContext {
    pub fn new() -> EvalContext {
        EvalContext {
            vars: HashMap::new(),
            match_name: "MATCHES".to_string(),
            request: Request::new(Method::GET, "http://localhost"),
        }
    }
    pub fn new_with_vars(vars: HashMap<String, Value>) -> EvalContext {
        EvalContext {
            vars,
            match_name: "MATCHES".to_string(),
            request: Request::new(Method::GET, "http://localhost"),
        }
    }
    pub fn get_variable(&self, key: &str, subkey: Option<String>) -> Value {
        match key {
            "HTTP_HOST" => match self.request.get_header("host") {
                Some(h) => Value::String(h.to_str().unwrap_or_else(|_| "").to_string()),
                None => Value::Null,
            },
            "REQUEST_METHOD" => Value::String(self.request.get_method_str().to_string()),
            "QUERY_STRING" => match self.request.get_query_str() {
                Some(s) => Value::String(s.to_string()),
                None => Value::Null,
            },
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
    fn from(data: [(String, Value); N]) -> EvalContext {
        EvalContext::new_with_vars(HashMap::from(data))
    }
}

fn format_key(key: &str, subkey: Option<String>) -> String {
    match subkey {
        Some(subkey) => format!("{}[{}]", key, subkey),
        None => format!("{}", key),
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Integer(i64),
    String(String),
    Error(String),
    Boolean(BoolValue),
    Null,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BoolValue {
    True,
    False,
}

impl Value {
    pub fn to_bool(&self) -> bool {
        match self {
            Value::Integer(_) => true, // TODO: make sure 0 isn't falsey
            Value::String(_) => true,
            Value::Error(_) => false,
            Value::Boolean(b) => *b == BoolValue::True,
            Value::Null => false,
        }
    }

    pub fn to_string(&self) -> String {
        match self {
            Value::Integer(i) => i.to_string(),
            Value::String(s) => s.clone(),
            Value::Boolean(_) => "".to_string(), // TODO: not sure if this is right
            Value::Error(_) => "".to_string(),
            Value::Null => "".to_string(),
        }
    }
}

fn eval_expr(expr: Expr, ctx: &mut EvalContext) -> Result<Value> {
    let result = match expr {
        Expr::Integer(i) => Value::Integer(i),
        Expr::String(s) => Value::String(s),
        Expr::Variable(key, subkey) => ctx.get_variable(&key, subkey).clone(),
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
                            let capval = match cap {
                                Some(s) => Value::String(s.as_str().to_string()),
                                None => Value::Null,
                            };
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
            call_dispatch(identifier, values)?
        }
    };
    Ok(result)
}

fn call_dispatch(identifier: String, args: Vec<Value>) -> Result<Value> {
    match identifier.as_str() {
        "ping" => return Ok(Value::String("pong".to_string())),
        "lower" => {
            if args.len() != 1 {
                return Ok(Value::Error(
                    "wrong number of arguments to 'lower'".to_string(),
                ));
            } else {
                match &args[0] {
                    Value::String(s) => return Ok(Value::String(s.to_lowercase())),
                    _ => return Ok(Value::Error("incorrect type passed to 'lower'".to_string())),
                }
            }
        }
        "html_encode" => {
            if args.len() != 1 {
                return Ok(Value::Error(
                    "wrong number of arguments to 'html_encode'".to_string(),
                ));
            } else {
                match &args[0] {
                    Value::String(s) => {
                        return Ok(Value::String(html_escape::encode_text(s).to_string()))
                    }
                    _ => {
                        return Ok(Value::Error(
                            "incorrect type passed to 'html_encode'".to_string(),
                        ))
                    }
                }
            }
        }
        "replace" => {
            if args.len() < 3 {
                return Ok(Value::Error(
                    "wrong number of arguments to 'replace'".to_string(),
                ));
            } else {
                let Value::String(haystack) = &args[0] else {
                    return Ok(Value::Error(
                        "incorrect type passed to 'replace'".to_string(),
                    ));
                };
                let Value::String(needle) = &args[1] else {
                    return Ok(Value::Error(
                        "incorrect type passed to 'replace'".to_string(),
                    ));
                };
                let Value::String(replacement) = &args[2] else {
                    return Ok(Value::Error(
                        "incorrect type passed to 'replace'".to_string(),
                    ));
                };

                if args.len() == 4 {
                    let Value::Integer(count) = &args[3] else {
                        return Ok(Value::Error(
                            "incorrect type passed to 'replace'".to_string(),
                        ));
                    };
                    let count: usize = *count as usize; // TODO: do this more safely

                    return Ok(Value::String(haystack.replacen(needle, replacement, count)));
                } else {
                    return Ok(Value::String(haystack.replace(needle, replacement)));
                }
            }
        }
        _ => return Ok(Value::Error(format!("unknown function: {}", identifier))),
    };
}

#[derive(Debug, Clone, PartialEq)]
enum Expr {
    Integer(i64),
    String(String),
    Variable(String, Option<String>),
    Comparison(Box<Comparison>),
    Call(String, Vec<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
struct Comparison {
    left: Expr,
    operator: Operator,
    right: Expr,
}

fn parse(tokens: Vec<Token>) -> Result<Expr> {
    let mut cur = tokens.iter().peekable();

    let expr = parse_expr(&mut cur)?;
    if cur.peek() != None {
        return Err(ExecutionError::ExpressionParseError(
            "expected eof".to_string(),
        ));
    }
    Ok(expr)
}
fn parse_expr(cur: &mut Peekable<Iter<Token>>) -> Result<Expr> {
    let node = if let Some(token) = cur.next() {
        match token {
            Token::Integer(i) => Expr::Integer(*i),
            Token::String(s) => Expr::String(s.clone()),
            Token::Variable(s, sub) => Expr::Variable(s.clone(), sub.clone()),
            Token::Identifier(s) => parse_call(s.clone(), cur)?,
            _ => {
                return Err(ExecutionError::ExpressionParseError(
                    "unexpected token starting expression".to_string(),
                ))
            }
        }
    } else {
        return Err(ExecutionError::ExpressionParseError(
            "unexpected end of tokens".to_string(),
        ));
    };

    // return if we've reached EOF or if we're possibly in an args list
    // TODO: I'm not sure this is the right approach, but here we are
    match cur.peek() {
        None => return Ok(node),
        Some(&&Token::Comma) | Some(&&Token::CloseParen) => return Ok(node),
        _ => {}
    }

    // We must have a Comparison
    let left = node;
    let operator = match cur.next().unwrap() {
        Token::Operator(op) => op,
        _ => {
            return Err(ExecutionError::ExpressionParseError(
                "expected operator".to_string(),
            ));
        }
    };
    let right = parse_expr(cur)?;

    let node = Expr::Comparison(Box::new(Comparison {
        left,
        operator: operator.clone(),
        right,
    }));

    Ok(node)
}

fn parse_call(identifier: String, cur: &mut Peekable<Iter<Token>>) -> Result<Expr> {
    match cur.next() {
        Some(Token::OpenParen) => {
            let mut args = Vec::new();
            loop {
                match cur.peek() {
                    Some(&&Token::CloseParen) => {
                        cur.next();
                        break;
                    }
                    _ => {
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
                                return Err(ExecutionError::ExpressionParseError(
                                    "unexpected token in arg list".to_string(),
                                ))
                            }
                        }
                    }
                }
            }
            Ok(Expr::Call(identifier, args))
        }
        _ => {
            return Err(ExecutionError::ExpressionParseError(
                "unexpected token following identifier".to_string(),
            ))
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Token {
    Integer(i64),
    String(String),
    Variable(String, Option<String>),
    Operator(Operator),
    Identifier(String),
    OpenParen,
    CloseParen,
    Comma,
}

#[derive(Debug, Clone, PartialEq)]
enum Operator {
    Matches,
    MatchesInsensitive,
}

fn lex_expr(expr: String) -> Result<Vec<Token>> {
    let mut result = Vec::new();

    let mut cur = expr.chars().peekable();
    while let Some(c) = cur.peek() {
        match c {
            '\'' => {
                cur.next();
                result.push(get_string(&mut cur)?);
            }
            '$' => {
                cur.next();
                match cur.peek() {
                    Some(pc) => {
                        let pc = *pc;
                        match pc {
                            '(' => {
                                cur.next();
                                result.push(get_variable(&mut cur)?);
                            }
                            'a'..='z' => {
                                result.push(get_identifier(&mut cur));
                            }
                            _ => return Err(ExecutionError::ExpressionParseError(expr)),
                        }
                    }

                    // TODO: make these errors more useful, i.e. point to the problem
                    _ => return Err(ExecutionError::ExpressionParseError(expr)),
                }
            }
            '0'..='9' | '-' => {
                result.push(get_integer(&mut cur)?);
            }
            'a'..='z' => {
                // word operator
                result.push(get_word_operator(&mut cur)?);
            }
            '=' | '!' | '<' | '>' | '|' | '&' => {
                // TODO: normal operator
                return Err(ExecutionError::ExpressionParseError(expr));
            }
            '(' => {
                cur.next();
                result.push(Token::OpenParen);
            }
            ')' => {
                cur.next();
                result.push(Token::CloseParen);
            }
            ',' => {
                cur.next();
                result.push(Token::Comma);
            }
            ' ' => {
                cur.next();
            }
            _ => return Err(ExecutionError::ExpressionParseError(expr)),
        }
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
        match *c {
            '0'..='9' => {
                return Err(ExecutionError::ExpressionParseError(
                    "invalid number".to_string(),
                ))
            }
            _ => {}
        }
    }

    if c == '-' {
        let Some(c) = cur.next() else {
            return Err(ExecutionError::ExpressionParseError(
                "invalid number".to_string(),
            ));
        };
        match c {
            '1'..='9' => buf.push(c),
            _ => {
                return Err(ExecutionError::ExpressionParseError(
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
        return Err(ExecutionError::ExpressionParseError(
            "invalid number".to_string(),
        ));
    };
    Ok(Token::Integer(num))
}

fn get_identifier(cur: &mut Peekable<Chars>) -> Token {
    let mut buf = Vec::new();

    while let Some(c) = cur.peek() {
        match c {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '_' => {
                buf.push(cur.next().unwrap());
            }
            _ => break,
        }
    }
    Token::Identifier(buf.into_iter().collect())
}

fn get_word_operator(cur: &mut Peekable<Chars>) -> Result<Token> {
    let mut buf = Vec::new();
    buf.push(cur.next().unwrap());

    while let Some(c) = cur.next() {
        match c {
            'a'..='z' | '0'..='9' | '_' => buf.push(c),
            _ => break,
        }
    }
    let s: String = buf.into_iter().collect();
    match s.as_str() {
        "matches" => Ok(Token::Operator(Operator::Matches)),
        "matches_i" => Ok(Token::Operator(Operator::MatchesInsensitive)),
        _ => Err(ExecutionError::ExpressionParseError(s)),
    }
}

fn get_string(cur: &mut Peekable<Chars>) -> Result<Token> {
    // TODO: handle escaping
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
            cur.next();
            return Ok(Token::String("".to_string()));
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
                    } else {
                        // Just two ticks
                        buf.push(c);
                        buf.push(c2);
                    }
                } else {
                    // error
                    return Err(ExecutionError::ExpressionParseError(
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
                        return Err(ExecutionError::ExpressionParseError(
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

fn get_variable(cur: &mut Peekable<Chars>) -> Result<Token> {
    let mut buf = Vec::new();
    let mut subscript_buf = Vec::new();
    let mut has_subscript = false;

    while let Some(c) = cur.next() {
        match c {
            ')' => break,
            '{' => {
                has_subscript = true;
                while let Some(c) = cur.next() {
                    match c {
                        '}' => break,
                        _ => subscript_buf.push(c),
                    }
                }
            }
            _ => buf.push(c),
        }
    }
    let subscript = if has_subscript {
        Some(subscript_buf.into_iter().collect())
    } else {
        None
    };

    Ok(Token::Variable(buf.into_iter().collect(), subscript))
}

#[cfg(test)]
mod tests {
    use super::*;
    use regex::Regex;

    #[test]
    fn test_lex_integer() -> Result<()> {
        let tokens = lex_expr("1 23 456789 0 -987654 -32 -1 0".to_string())?;
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
    fn test_lex_simple_string() -> Result<()> {
        let tokens = lex_expr("'hello'".to_string())?;
        assert_eq!(tokens, vec![Token::String("hello".to_string())]);
        Ok(())
    }
    #[test]
    fn test_lex_escaped_string() -> Result<()> {
        let tokens = lex_expr(r#"'hel\'lo'"#.to_string())?;
        assert_eq!(tokens, vec![Token::String("hel\'lo".to_string())]);
        Ok(())
    }
    #[test]
    fn test_lex_triple_tick_string() -> Result<()> {
        let tokens = lex_expr(r#"'''h'el''l\'o\'''"#.to_string())?;
        assert_eq!(tokens, vec![Token::String(r#"h'el''l\'o\"#.to_string())]);
        Ok(())
    }
    #[test]
    fn test_lex_triple_tick_and_escaping_torture() -> Result<()> {
        let tokens = lex_expr(r#"'\\\'triple\'/' matches '''\'triple'/'''"#.to_string())?;
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
        let tokens = lex_expr("$(hello)".to_string())?;
        assert_eq!(tokens, vec![Token::Variable("hello".to_string(), None)]);
        Ok(())
    }
    #[test]
    fn test_lex_variable_with_subscript() -> Result<()> {
        let tokens = lex_expr("$(hello{goodbye})".to_string())?;
        assert_eq!(
            tokens,
            vec![Token::Variable(
                "hello".to_string(),
                Some("goodbye".to_string())
            )]
        );
        Ok(())
    }
    #[test]
    fn test_lex_variable_with_integer_subscript() -> Result<()> {
        let tokens = lex_expr("$(hello{6})".to_string())?;
        assert_eq!(
            tokens,
            vec![Token::Variable("hello".to_string(), Some("6".to_string()))]
        );
        Ok(())
    }
    #[test]
    fn test_lex_matches_operator() -> Result<()> {
        let tokens = lex_expr("matches".to_string())?;
        assert_eq!(tokens, vec![Token::Operator(Operator::Matches)]);
        Ok(())
    }
    #[test]
    fn test_lex_matches_i_operator() -> Result<()> {
        let tokens = lex_expr("matches_i".to_string())?;
        assert_eq!(tokens, vec![Token::Operator(Operator::MatchesInsensitive)]);
        Ok(())
    }
    #[test]
    fn test_lex_identifier() -> Result<()> {
        let tokens = lex_expr("$foo2BAZ".to_string())?;
        assert_eq!(tokens, vec![Token::Identifier("foo2BAZ".to_string())]);
        Ok(())
    }
    #[test]
    fn test_lex_simple_call() -> Result<()> {
        let tokens = lex_expr("$fn()".to_string())?;
        assert_eq!(
            tokens,
            vec![
                Token::Identifier("fn".to_string()),
                Token::OpenParen,
                Token::CloseParen
            ]
        );
        Ok(())
    }
    #[test]
    fn test_lex_call_with_arg() -> Result<()> {
        let tokens = lex_expr("$fn('hello')".to_string())?;
        assert_eq!(
            tokens,
            vec![
                Token::Identifier("fn".to_string()),
                Token::OpenParen,
                Token::String("hello".to_string()),
                Token::CloseParen
            ]
        );
        Ok(())
    }
    #[test]
    fn test_lex_call_with_two_args() -> Result<()> {
        let tokens = lex_expr("$fn($(hello), 'hello')".to_string())?;
        assert_eq!(
            tokens,
            vec![
                Token::Identifier("fn".to_string()),
                Token::OpenParen,
                Token::Variable("hello".to_string(), None),
                Token::Comma,
                Token::String("hello".to_string()),
                Token::CloseParen
            ]
        );
        Ok(())
    }
    #[test]
    fn test_lex_comparison() -> Result<()> {
        let tokens = lex_expr("$(foo) matches 'bar'".to_string())?;
        assert_eq!(
            tokens,
            vec![
                Token::Variable("foo".to_string(), None),
                Token::Operator(Operator::Matches),
                Token::String("bar".to_string())
            ]
        );
        Ok(())
    }

    #[test]
    fn test_lex_error() -> Result<()> {
        let token_result = lex_expr("fwej".to_string());
        assert!(token_result.is_err());
        Ok(())
    }

    #[test]
    fn test_parse_integer() -> Result<()> {
        let tokens = lex_expr("1".to_string())?;
        let expr = parse(tokens)?;
        assert_eq!(expr, Expr::Integer(1));
        Ok(())
    }
    #[test]
    fn test_parse_simple_string() -> Result<()> {
        let tokens = lex_expr("'hello'".to_string())?;
        let expr = parse(tokens)?;
        assert_eq!(expr, Expr::String("hello".to_string()));
        Ok(())
    }
    #[test]
    fn test_parse_variable() -> Result<()> {
        let tokens = lex_expr("$(hello)".to_string())?;
        let expr = parse(tokens)?;
        assert_eq!(expr, Expr::Variable("hello".to_string(), None));
        Ok(())
    }

    #[test]
    fn test_parse_comparison() -> Result<()> {
        let tokens = lex_expr("$(foo) matches 'bar'".to_string())?;
        let expr = parse(tokens)?;
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
        let tokens = lex_expr("$hello()".to_string())?;
        let expr = parse(tokens)?;
        assert_eq!(expr, Expr::Call("hello".to_string(), Vec::new()));
        Ok(())
    }
    #[test]
    fn test_parse_call_with_arg() -> Result<()> {
        let tokens = lex_expr("$fn('hello')".to_string())?;
        let expr = parse(tokens)?;
        assert_eq!(
            expr,
            Expr::Call("fn".to_string(), vec![Expr::String("hello".to_string())])
        );
        Ok(())
    }
    #[test]
    fn test_parse_call_with_two_args() -> Result<()> {
        let tokens = lex_expr("$fn($(hello), 'hello')".to_string())?;
        let expr = parse(tokens)?;
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
        let expr = Expr::Variable("hello".to_string(), Some("abc".to_string()));
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
            "$(hello) matches '^foo'".to_string(),
            &mut EvalContext::from([("hello".to_string(), Value::String("foobar".to_string()))]),
        )?;
        assert_eq!(result, Value::Boolean(BoolValue::True));
        Ok(())
    }
    #[test]
    fn test_eval_matches_i_comparison() -> Result<()> {
        let result = evaluate_expression(
            "$(hello) matches_i '^foo'".to_string(),
            &mut EvalContext::from([("hello".to_string(), Value::String("FOOBAR".to_string()))]),
        )?;
        assert_eq!(result, Value::Boolean(BoolValue::True));
        Ok(())
    }
    #[test]
    fn test_eval_matches_with_captures() -> Result<()> {
        let mut ctx =
            &mut EvalContext::from([("hello".to_string(), Value::String("foobar".to_string()))]);

        let result = evaluate_expression("$(hello) matches '^(fo)o'".to_string(), &mut ctx)?;
        assert_eq!(result, Value::Boolean(BoolValue::True));

        let result = evaluate_expression("$(MATCHES{1})".to_string(), &mut ctx)?;
        assert_eq!(result, Value::String("fo".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_matches_with_captures_and_match_name() -> Result<()> {
        let mut ctx =
            &mut EvalContext::from([("hello".to_string(), Value::String("foobar".to_string()))]);

        ctx.set_match_name("my_custom_name");
        let result = evaluate_expression("$(hello) matches '^(fo)o'".to_string(), ctx)?;
        assert_eq!(result, Value::Boolean(BoolValue::True));

        let result = evaluate_expression("$(my_custom_name{1})".to_string(), &mut ctx)?;
        assert_eq!(result, Value::String("fo".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_matches_comparison_negative() -> Result<()> {
        let result = evaluate_expression(
            "$(hello) matches '^foo'".to_string(),
            &mut EvalContext::from([("hello".to_string(), Value::String("nope".to_string()))]),
        )?;
        assert_eq!(result, Value::Boolean(BoolValue::False));
        Ok(())
    }
    #[test]
    fn test_eval_function_call() -> Result<()> {
        let result = evaluate_expression("$ping()".to_string(), &mut EvalContext::new())?;
        assert_eq!(result, Value::String("pong".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_lower_call() -> Result<()> {
        let result = evaluate_expression("$lower('FOO')".to_string(), &mut EvalContext::new())?;
        assert_eq!(result, Value::String("foo".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_html_encode_call() -> Result<()> {
        let result = evaluate_expression(
            "$html_encode('a > b < c')".to_string(),
            &mut EvalContext::new(),
        )?;
        assert_eq!(result, Value::String("a &gt; b &lt; c".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_replace_call() -> Result<()> {
        let result = evaluate_expression(
            "$replace('abc-def-ghi-', '-', '==')".to_string(),
            &mut EvalContext::new(),
        )?;
        assert_eq!(result, Value::String("abc==def==ghi==".to_string()));
        Ok(())
    }

    #[test]
    fn test_eval_replace_call_with_count() -> Result<()> {
        let result = evaluate_expression(
            "$replace('abc-def-ghi-', '-', '==', 2)".to_string(),
            &mut EvalContext::new(),
        )?;
        assert_eq!(result, Value::String("abc==def==ghi-".to_string()));
        Ok(())
    }

    #[test]
    fn test_eval_get_request_metadata_method() -> Result<()> {
        let mut ctx = EvalContext::new();
        let result = evaluate_expression("$(REQUEST_METHOD)".to_string(), &mut ctx)?;
        assert_eq!(result, Value::String("GET".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_get_request_metadata_query() -> Result<()> {
        let mut ctx = EvalContext::new();
        ctx.set_request(Request::new(Method::GET, "http://localhost?hello"));

        let result = evaluate_expression("$(QUERY_STRING)".to_string(), &mut ctx)?;
        assert_eq!(result, Value::String("hello".to_string()));
        Ok(())
    }
}
