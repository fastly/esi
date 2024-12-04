use std::iter::Peekable;
use std::str::Chars;

use crate::{ExecutionError, Result, Value, Variables};

pub fn evaluate_expression(raw_expr: String, ctx: EvalContext) -> Result<Value> {
    // TODO: this got real ugly, figure out some better way to do this
    let tokens = match lex_expr(raw_expr) {
        Ok(r) => r,
        Err(ExecutionError::ExpressionParseError(s)) => return Ok(Value::Error(s)),
        Err(e) => return Err(e),
    };
    let expr = match parse_expr(tokens) {
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

pub struct EvalContext<'a> {
    variables: &'a Variables,
    // request context
}
impl EvalContext<'_> {
    pub fn new(variables: &Variables) -> EvalContext {
        EvalContext { variables }
    }
}

fn eval_expr(expr: Expr, ctx: EvalContext) -> Result<Value> {
    let result = match expr {
        Expr::String(s) => Value::String(s),
        Expr::Variable(s) => ctx.variables.get(&s).clone(),
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
                    // TODO: make these errors more useful, i.e. point to the problem
                    _ => return Err(ExecutionError::ExpressionParseError(expr)),
                }
            }
            _ => return Err(ExecutionError::ExpressionParseError(expr)),
        }
    }

    Ok(result)
}

fn get_string(cur: &mut Peekable<Chars>) -> Token {
    // TODO: handle escaping
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
        let result = eval_expr(expr, EvalContext::new(&Variables::new()))?;
        assert_eq!(result, Value::String("hello".to_string()));
        Ok(())
    }

    #[test]
    fn test_eval_variable() -> Result<()> {
        let expr = Expr::Variable("hello".to_string());
        let result = eval_expr(
            expr,
            EvalContext::new(&Variables::from([(
                "hello".to_string(),
                Value::String("goodbye".to_string()),
            )])),
        )?;
        assert_eq!(result, Value::String("goodbye".to_string()));
        Ok(())
    }

    // TODO: more negative tests
    #[test]
    fn test_evaluation_error() -> Result<()> {
        let result = evaluate_expression(
            "$hello".to_string(),
            EvalContext::new(&Variables::from([(
                "hello".to_string(),
                Value::String("goodbye".to_string()),
            )])),
        )?;
        assert_eq!(result, Value::Error("$hello".to_string()));
        Ok(())
    }
}
