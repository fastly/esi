use bytes::Bytes;

/// Dynamic Content Assembly mode for esi:include and esi:eval
#[derive(Default, Debug, PartialEq, Clone, Copy)]
pub enum DcaMode {
    #[default]
    /// No pre-processing (default) - fragment returned as-is
    None,
    /// Fragment is processed as ESI by origin before returning
    Esi,
}

/// All attributes for esi:include tags
#[derive(Debug, PartialEq, Clone)]
pub struct IncludeAttributes {
    /// Source URL to fetch (required)
    pub src: Expr,
    /// Optional fallback URL if src fails
    pub alt: Option<Expr>,
    /// Whether to continue on error (from onerror="continue")
    pub continue_on_error: bool,
    /// Dynamic Content Assembly mode - controls pre-processing
    pub dca: DcaMode,
    /// Time-To-Live for caching (e.g., "120m", "1h", "2d", "0s")
    pub ttl: Option<String>,
    /// Timeout in milliseconds for the request
    pub maxwait: Option<u32>,
    /// Whether to bypass caching (no-store)
    pub no_store: bool,
    /// HTTP method (GET or POST)
    pub method: Option<Expr>,
    /// POST request body
    pub entity: Option<Expr>,
    /// Headers to append to the request
    pub appendheaders: Vec<(String, Expr)>,
    /// Headers to remove from the request
    pub removeheaders: Vec<String>,
    /// Headers to set on the request (replaces existing)
    pub setheaders: Vec<(String, Expr)>,
    /// Child <esi:param> elements for query parameters
    pub params: Vec<(String, Expr)>,
}

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
        /// All include tag attributes (including params)
        attrs: IncludeAttributes,
    },
    Eval {
        /// All eval tag attributes (same as include but no alt)
        attrs: IncludeAttributes,
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
    Function {
        name: String,
        body: Vec<Element>,
    },
    Return {
        value: Expr,
    },
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
    // Comparison operators
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
    // Logical operators
    And,
    Or,
    // Arithmetic operators
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    // Range operator (for list creation)
    Range,
}
