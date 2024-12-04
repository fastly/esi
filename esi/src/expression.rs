use std::collections::HashMap;
use std::iter::Peekable;
use std::str::Chars;

use crate::{ExecutionError, Result};

pub fn evaluate_expression(raw_expr: String, ctx: EvalContext) -> Result<EvalResult> {
    let tokens = match lex_expr(raw_expr) {
        Ok(r) => r,
        Err(ExecutionError::ExpressionParseError(s)) => return Ok(EvalResult::Error(s)),
        Err(e) => return Err(e),
    };
    let expr = match parse_expr(tokens) {
        Ok(r) => r,
        Err(ExecutionError::ExpressionParseError(s)) => return Ok(EvalResult::Error(s)),
        Err(e) => return Err(e),
    };
    match eval_expr(expr, ctx) {
        Ok(r) => Ok(r),
        Err(ExecutionError::ExpressionParseError(s)) => return Ok(EvalResult::Error(s)),
        Err(e) => return Err(e),
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum EvalResult {
    String(String),
    Error(String),
}

pub struct EvalContext<'a> {
    variables: &'a HashMap<String, String>,
    // request context
}
impl EvalContext<'_> {
    pub fn new(variables: &HashMap<String, String>) -> EvalContext {
        EvalContext { variables }
    }
}

fn eval_expr(expr: Expr, ctx: EvalContext) -> Result<EvalResult> {
    let result = match expr {
        Expr::String(s) => EvalResult::String(s),
        Expr::Variable(s) => match ctx.variables.get(&s) {
            Some(value) => EvalResult::String(value.to_owned()),
            None => EvalResult::String("".to_string()),
        },
    };
    Ok(result)
}

#[derive(Debug, Clone, PartialEq)]
enum Expr {
    String(String),
    Variable(String),
}

fn parse_expr(tokens: Vec<Token>) -> Result<Expr> {
    let mut cur = tokens.iter();

    let node = if let Some(token) = cur.next() {
        match token {
            Token::String(s) => Expr::String(s.clone()),
            Token::Variable(s) => Expr::Variable(s.clone()),
        }
    } else {
        return Err(ExecutionError::ExpressionParseError(
            "unexpected end of tokens".to_string(),
        ));
    };

    Ok(node)
}

#[derive(Debug, Clone, PartialEq)]
enum Token {
    String(String),
    Variable(String),
}

fn lex_expr(expr: String) -> Result<Vec<Token>> {
    let mut result = Vec::new();

    let mut cur = expr.chars().peekable();
    while let Some(c) = cur.peek() {
        match c {
            '\'' => {
                cur.next();
                result.push(get_string(&mut cur));
            }
            '$' => {
                cur.next();
                match cur.peek() {
                    Some(&'(') => {
                        cur.next();
                        result.push(get_variable(&mut cur));
                    }
                    _ => return Err(ExecutionError::ExpressionParseError(expr)),
                }
            }
            _ => return Err(ExecutionError::ExpressionParseError(expr)),
        }
    }

    Ok(result)
}

fn get_string(cur: &mut Peekable<Chars>) -> Token {
    let mut buf = Vec::new();

    while let Some(c) = cur.next() {
        match c {
            '\'' => break,
            _ => buf.push(c),
        }
    }
    Token::String(buf.into_iter().collect())
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
    fn test_lex_variable() -> Result<()> {
        let tokens = lex_expr("$(hello)".to_string())?;
        assert_eq!(tokens, vec![Token::Variable("hello".to_string())]);
        Ok(())
    }

    #[test]
    fn test_parse_simple_string() -> Result<()> {
        let tokens = lex_expr("'hello'".to_string())?;
        let expr = parse_expr(tokens)?;
        assert_eq!(expr, Expr::String("hello".to_string()));
        Ok(())
    }

    #[test]
    fn test_parse_variable() -> Result<()> {
        let tokens = lex_expr("$(hello)".to_string())?;
        let expr = parse_expr(tokens)?;
        assert_eq!(expr, Expr::Variable("hello".to_string()));
        Ok(())
    }

    #[test]
    fn test_eval_string() -> Result<()> {
        let expr = Expr::String("hello".to_string());
        let result = eval_expr(
            expr,
            EvalContext {
                variables: &HashMap::new(),
            },
        )?;
        assert_eq!(result, EvalResult::String("hello".to_string()));
        Ok(())
    }

    #[test]
    fn test_eval_variable() -> Result<()> {
        let expr = Expr::Variable("hello".to_string());
        let result = eval_expr(
            expr,
            EvalContext {
                variables: &HashMap::from([("hello".to_string(), "goodbye".to_string())]),
            },
        )?;
        assert_eq!(result, EvalResult::String("goodbye".to_string()));
        Ok(())
    }

    #[test]
    fn test_evaluation_error() -> Result<()> {
        let result = evaluate_expression(
            "$hello".to_string(),
            EvalContext::new(&HashMap::from([(
                "hello".to_string(),
                "goodbye".to_string(),
            )])),
        )?;
        assert_eq!(result, EvalResult::Error("$hello".to_string()));
        Ok(())
    }
}
