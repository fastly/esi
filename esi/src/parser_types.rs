#[derive(Debug, PartialEq, Clone)]
pub enum Tag<'a> {
    Include(Vec<(&'a str, &'a str)>),
    Choose(Vec<Chunk<'a>>, Option<Vec<Chunk<'a>>>),
    When(Expr<'a>, Vec<Chunk<'a>>),
    Otherwise(Vec<Chunk<'a>>),
    Try(Vec<Vec<Chunk<'a>>>, Option<Vec<Chunk<'a>>>),
    Attempt(Vec<Chunk<'a>>),
    Except(Vec<Chunk<'a>>),
    Assign(Vec<(&'a str, &'a str)>, Option<Vec<Chunk<'a>>>),
}

#[derive(Debug, PartialEq, Clone)]
pub enum Symbol<'e> {
    Function {
        name: &'e str,
        args: Vec<Symbol<'e>>,
    },
    Variable {
        name: &'e str,
        key: Option<&'e str>,
        default: Option<Box<Symbol<'e>>>,
    },
    String(Option<&'e str>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Ast<'a>(pub Vec<Chunk<'a>>);

#[derive(Debug, PartialEq, Clone)]
pub enum Chunk<'a> {
    Esi(Tag<'a>),
    Expr(Expr<'a>),
    Html(&'a str),
    Text(&'a str),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr<'a> {
    Integer(i32),
    String(Option<&'a str>),
    Variable(&'a str, Option<&'a str>, Option<Box<Expr<'a>>>),
    Comparison {
        left: Box<Expr<'a>>,
        operator: Operator,
        right: Box<Expr<'a>>,
    },
    Call(&'a str, Vec<Expr<'a>>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Operator {
    Matches,
    MatchesInsensitive,
}
