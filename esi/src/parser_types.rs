/// Represents a single when branch in a choose block
#[derive(Debug, PartialEq, Clone)]
pub struct WhenBranch<'a> {
    pub test: Expr<'a>,
    pub match_name: Option<String>,
    pub content: Vec<Element<'a>>,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Tag<'a> {
    Include {
        src: String,
        alt: Option<String>,
        continue_on_error: bool,
    },
    Try {
        attempt_events: Vec<Vec<Element<'a>>>,
        except_events: Vec<Element<'a>>,
    },
    Assign {
        name: &'a str,
        value: Expr<'a>,
    },
    Vars {
        name: Option<String>,
    },
    When {
        test: &'a str,
        match_name: Option<String>,
    },
    Choose {
        when_branches: Vec<WhenBranch<'a>>,
        otherwise_events: Vec<Element<'a>>,
    },
    Attempt(Vec<Element<'a>>),
    Except(Vec<Element<'a>>),
    Otherwise,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Element<'a> {
    Esi(Tag<'a>),
    Expr(Expr<'a>),
    Html(&'a str),
    Text(&'a str),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr<'a> {
    Integer(i32),
    String(Option<&'a str>),
    Variable(&'a str, Option<Box<Expr<'a>>>, Option<Box<Expr<'a>>>),
    Comparison {
        left: Box<Expr<'a>>,
        operator: Operator,
        right: Box<Expr<'a>>,
    },
    Call(&'a str, Vec<Expr<'a>>),
    Not(Box<Expr<'a>>),
    /// Represents a compound expression with interpolated text and expressions
    /// Used for cases like: <esi:assign name="x">prefix$(VAR)suffix</esi:assign>
    Interpolated(Vec<Element<'a>>),
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
