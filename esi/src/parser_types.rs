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
        src: String,
        alt: Option<String>,
        continue_on_error: bool,
    },
    Try {
        attempt_events: Vec<Vec<Element>>,
        except_events: Vec<Element>,
    },
    Assign {
        name: String,
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
}

#[derive(Debug, Clone, PartialEq)]
pub enum Operator {
    Matches,
    MatchesInsensitive,
    Equals,
    NotEquals,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    And,
    Or,
}
