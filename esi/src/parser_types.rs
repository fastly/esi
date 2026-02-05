use bytes::Bytes;

/// Represents a single when branch in a choose block
#[derive(Debug, PartialEq, Clone)]
pub struct WhenBranch {
    pub test: Expr,
    pub match_name: Option<String>,
    pub content: Vec<Element>,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Tag {
    Include {
        src: Expr,
        alt: Option<Expr>,
        continue_on_error: bool,
        params: Vec<(String, Expr)>,
    },
    Try {
        attempt_events: Vec<Vec<Element>>,
        except_events: Vec<Element>,
    },
    Assign {
        name: String,
        subscript: Option<Expr>,
        value: Expr,
    },
    Vars {
        name: Option<String>,
    },
    When {
        test: String,
        match_name: Option<String>,
    },
    Choose {
        when_branches: Vec<WhenBranch>,
        otherwise_events: Vec<Element>,
    },
    Attempt(Vec<Element>),
    Except(Vec<Element>),
    Otherwise,
    Foreach {
        collection: Expr,
        item: Option<String>,
        content: Vec<Element>,
    },
    Break,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Element {
    Esi(Tag),
    Expr(Expr),
    Html(Bytes),
    Text(Bytes),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Integer(i32),
    String(Option<String>),
    Variable(String, Option<Box<Expr>>, Option<Box<Expr>>),
    Comparison {
        left: Box<Expr>,
        operator: Operator,
        right: Box<Expr>,
    },
    Call(String, Vec<Expr>),
    Not(Box<Expr>),
    /// Represents a compound expression with interpolated text and expressions
    /// Used for cases like: <esi:assign name="x">prefix$(VAR)suffix</esi:assign>
    Interpolated(Vec<Element>),
    /// Dictionary literal: {key:value, key:value}
    DictLiteral(Vec<(Expr, Expr)>),
    /// List literal: [value, value]
    ListLiteral(Vec<Expr>),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Operator {
    Matches,
    MatchesInsensitive,
    Has,
    HasInsensitive,
    Equals,
    NotEquals,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    And,
    Or,
}
