use regex::Regex;
use std::iter::Peekable;
use std::slice::Iter;
use std::str::Chars;

use crate::{BoolValue, ExecutionError, Result, Value, Variables};

pub fn evaluate_expression(raw_expr: String, ctx: EvalContext) -> Result<Value> {
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
    match eval_expr(expr, &ctx) {
        Ok(r) => Ok(r),
        Err(ExecutionError::ExpressionParseError(s)) => return Ok(Value::Error(s)),
        Err(e) => return Err(e),
    }
}

pub struct EvalContext<'a> {
    variables: &'a Variables,
    // request content for metadata
}
impl EvalContext<'_> {
    pub fn new(variables: &Variables) -> EvalContext {
        EvalContext { variables }
    }
}

fn eval_expr(expr: Expr, ctx: &EvalContext) -> Result<Value> {
    let result = match expr {
        Expr::String(s) => Value::String(s),
        Expr::Variable(s) => ctx.variables.get(&s).clone(),
        Expr::Comparison(c) => {
            let left = eval_expr(c.left, ctx)?;
            let right = eval_expr(c.right, ctx)?;
            match c.operator {
                Operator::Matches => match (left, right) {
                    (Value::String(test), Value::String(pattern)) => {
                        let re = Regex::new(&pattern)?;
                        if re.is_match(&test) {
                            Value::Boolean(BoolValue::True)
                        } else {
                            Value::Boolean(BoolValue::False)
                        }
                    }
                    _ => {
                        return Err(ExecutionError::ExpressionParseError(
                            "incorrect types".to_string(),
                        ));
                    }
                },
                Operator::MatchesInsensitive => todo!(),
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
    let result = match identifier.as_str() {
        "ping" => Value::String("pong".to_string()),
        "lower" => {
            if args.len() != 1 {
                Value::Error("wrong number of arguments to 'lower'".to_string())
            } else {
                match &args[0] {
                    Value::String(s) => Value::String(s.to_lowercase()),
                    _ => Value::Error("incorrect type passed to 'lower'".to_string()),
                }
            }
        }
        _ => Value::Error(format!("unknown function: {}", identifier)),
    };
    Ok(result)
}

#[derive(Debug, Clone, PartialEq)]
enum Expr {
    String(String),
    Variable(String),
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
            Token::String(s) => Expr::String(s.clone()),
            Token::Variable(s) => Expr::Variable(s.clone()),
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
    String(String),
    Variable(String),
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
                                result.push(get_variable(&mut cur));
                            }
                            'a'..='z' => {
                                result.push(get_identifier(&mut cur));
                            }
                            'A'..='Z' => {
                                // TODO: metadata identifier
                                return Err(ExecutionError::ExpressionParseError(expr));
                            }
                            _ => return Err(ExecutionError::ExpressionParseError(expr)),
                        }
                    }

                    // TODO: make these errors more useful, i.e. point to the problem
                    _ => return Err(ExecutionError::ExpressionParseError(expr)),
                }
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

fn get_variable(cur: &mut Peekable<Chars>) -> Token {
    let mut buf = Vec::new();

    while let Some(c) = cur.next() {
        match c {
            ')' => break,
            _ => buf.push(c),
        }
    }
    Token::Variable(buf.into_iter().collect())
}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert_eq!(tokens, vec![Token::Variable("hello".to_string())]);
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
                Token::Variable("hello".to_string()),
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
                Token::Variable("foo".to_string()),
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
        assert_eq!(expr, Expr::Variable("hello".to_string()));
        Ok(())
    }
    #[test]
    fn test_parse_comparison() -> Result<()> {
        let tokens = lex_expr("$(foo) matches 'bar'".to_string())?;
        let expr = parse(tokens)?;
        assert_eq!(
            expr,
            Expr::Comparison(Box::new(Comparison {
                left: Expr::Variable("foo".to_string()),
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
                    Expr::Variable("hello".to_string()),
                    Expr::String("hello".to_string())
                ]
            )
        );
        Ok(())
    }

    #[test]
    fn test_eval_string() -> Result<()> {
        let expr = Expr::String("hello".to_string());
        let result = eval_expr(expr, &EvalContext::new(&Variables::new()))?;
        assert_eq!(result, Value::String("hello".to_string()));
        Ok(())
    }

    #[test]
    fn test_eval_variable() -> Result<()> {
        let expr = Expr::Variable("hello".to_string());
        let result = eval_expr(
            expr,
            &EvalContext::new(&Variables::from([(
                "hello".to_string(),
                Value::String("goodbye".to_string()),
            )])),
        )?;
        assert_eq!(result, Value::String("goodbye".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_matches_comparison() -> Result<()> {
        let result = evaluate_expression(
            "$(hello) matches '^foo'".to_string(),
            EvalContext::new(&Variables::from([(
                "hello".to_string(),
                Value::String("foobar".to_string()),
            )])),
        )?;
        assert_eq!(result, Value::Boolean(BoolValue::True));
        Ok(())
    }
    #[test]
    fn test_eval_matches_comparison_negative() -> Result<()> {
        let result = evaluate_expression(
            "$(hello) matches '^foo'".to_string(),
            EvalContext::new(&Variables::from([(
                "hello".to_string(),
                Value::String("nope".to_string()),
            )])),
        )?;
        assert_eq!(result, Value::Boolean(BoolValue::False));
        Ok(())
    }
    #[test]
    fn test_eval_function_call() -> Result<()> {
        let result =
            evaluate_expression("$ping()".to_string(), EvalContext::new(&Variables::new()))?;
        assert_eq!(result, Value::String("pong".to_string()));
        Ok(())
    }
    #[test]
    fn test_eval_lower_call() -> Result<()> {
        let result = evaluate_expression(
            "$lower('FOO')".to_string(),
            EvalContext::new(&Variables::new()),
        )?;
        assert_eq!(result, Value::String("foo".to_string()));
        Ok(())
    }
}
