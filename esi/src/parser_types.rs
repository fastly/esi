use bytes::Bytes;

/// Dynamic Content Assembly mode for esi:include and esi:eval
#[derive(Default, Debug, PartialEq, Eq, Clone, Copy)]
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

/// A parsed ESI tag.
///
/// Each variant corresponds to an ESI processing instruction that was
/// recognised by the parser.  After parsing, the executor walks a tree of
/// [`Element`]s and dispatches on these variants to perform fetches,
/// evaluate conditions, iterate collections, and so on.
#[derive(Debug, PartialEq, Clone)]
pub enum Tag {
    /// `<esi:include src="…" />` – fetch a fragment and insert it into the
    /// response.  Supports fallback URLs, caching directives, custom
    /// headers, and POST bodies via [`IncludeAttributes`].
    Include {
        /// All include tag attributes (including child `<esi:param>` elements).
        attrs: IncludeAttributes,
    },

    /// `<esi:eval src="…" />` – fetch a fragment **and** recursively
    /// process it for ESI instructions before inserting it.
    /// Uses the same attribute set as `Include`.
    Eval {
        /// All eval tag attributes (same shape as include).
        attrs: IncludeAttributes,
    },

    /// `<esi:try>` – wrap an attempt/except pair so that fetch errors
    /// in the attempt block can be caught and replaced by the except
    /// block.
    ///
    /// `attempt_events` is a `Vec<Vec<Element>>` because the attempt
    /// may contain multiple independent include pipelines that are
    /// evaluated concurrently.
    Try {
        /// Content trees for each pipeline inside the `<esi:attempt>` block.
        attempt_events: Vec<Vec<Element>>,
        /// Fallback content rendered when the attempt fails.
        except_events: Vec<Element>,
    },

    /// `<esi:assign name="…">…</esi:assign>` – bind a variable in the
    /// current scope.  The value is an expression (possibly interpolated
    /// from the tag body).  An optional `subscript` sets a single key
    /// inside a dictionary variable.
    Assign {
        /// Variable name to assign to.
        name: String,
        /// Optional dictionary key (e.g. `name{key}`).
        subscript: Option<Expr>,
        /// Expression that produces the value to store.
        value: Expr,
    },

    /// `<esi:vars>…</esi:vars>` – evaluate ESI expressions in the
    /// enclosed text and emit the result.  An optional `name` attribute
    /// stores the result into a variable instead of emitting it.
    Vars {
        /// If present, the evaluated output is stored in this variable
        /// rather than written to the response.
        name: Option<String>,
    },

    /// A single `<esi:when test="…">` branch inside a `<esi:choose>`.
    /// Only used as an intermediate parse artifact before being folded
    /// into [`Tag::Choose`].
    When {
        /// The raw test expression string.
        test: String,
        /// Optional regex match capture name.
        match_name: Option<String>,
    },

    /// `<esi:choose>` – conditional logic.  The executor evaluates each
    /// `when` branch in order and renders the first whose test is truthy,
    /// falling back to the `otherwise` block if none match.
    Choose {
        /// Ordered list of `when` branches with their tests and content.
        when_branches: Vec<WhenBranch>,
        /// Content rendered when no `when` branch matches.
        otherwise_events: Vec<Element>,
    },

    /// Intermediate representation of an `<esi:attempt>` block.
    /// Folded into [`Tag::Try`] during tree construction.
    Attempt(Vec<Element>),

    /// Intermediate representation of an `<esi:except>` block.
    /// Folded into [`Tag::Try`] during tree construction.
    Except(Vec<Element>),

    /// Intermediate representation of an `<esi:otherwise>` block.
    /// Folded into [`Tag::Choose`] during tree construction.
    Otherwise,

    /// `<esi:foreach collection="…" item="…">…</esi:foreach>` – iterate
    /// over a list or dictionary, rendering the body once per element.
    Foreach {
        /// Expression that evaluates to the collection to iterate.
        collection: Expr,
        /// Loop variable name (defaults to `"item"` when absent).
        item: Option<String>,
        /// Body content rendered for each iteration.
        content: Vec<Element>,
    },

    /// `<esi:break />` – exit the innermost `foreach` loop early.
    Break,

    /// `<esi:function name="…">…</esi:function>` – define a named
    /// callable function whose body is a list of ESI elements.
    Function {
        /// Function name, callable via `$name(…)` expressions.
        name: String,
        /// The function body executed on each call.
        body: Vec<Element>,
    },

    /// `<esi:return value="…" />` – return a value from the current
    /// function.
    Return {
        /// Expression whose result becomes the function's return value.
        value: Expr,
    },
}

/// A parsed node in the ESI document tree.
///
/// Represents the four kinds of content the parser can produce:
/// structured ESI tags, dynamic expressions, raw HTML pass-through,
/// and plain-text content inside ESI constructs.
#[derive(Debug, PartialEq, Clone)]
pub enum Element {
    /// A structured ESI tag (e.g. `<esi:include>`, `<esi:choose>`).
    Esi(Tag),
    /// A dynamic ESI expression (e.g. `$(HTTP_HOST)`, `$(dict{'key'})`).
    Expr(Expr),
    /// Raw HTML markup passed through verbatim without interpretation.
    Html(Bytes),
    /// Plain-text content inside ESI constructs that participates in
    /// expression evaluation (e.g. assign bodies, interpolated segments).
    Content(Bytes),
}

/// An ESI expression AST node.
///
/// Produced by the expression parser for attribute values, `esi:vars`,
/// `esi:when` test conditions, and `esi:assign` bodies.  Evaluated at
/// runtime by `eval_expr` to produce
/// a `Value`.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// Integer literal (e.g. `42`, `-1`).
    Integer(i32),
    /// String literal (e.g. `'hello'`). `None` represents the empty string `''`.
    String(Option<Bytes>),
    /// Variable reference: name, optional subscript key, optional default value.
    /// e.g. `$(HTTP_HOST)`, `$(dict{'key'})`, `$(var|'default')`.
    Variable(String, Option<Box<Expr>>, Option<Box<Expr>>),
    /// Binary comparison or arithmetic: `left operator right`.
    Comparison {
        left: Box<Expr>,
        operator: Operator,
        right: Box<Expr>,
    },
    /// Function call: name and argument list (e.g. `$base64_encode(...)`).
    Call(String, Vec<Expr>),
    /// Logical negation: `!(expr)`.
    Not(Box<Expr>),
    /// Compound expression mixing literal text and embedded expressions.
    /// e.g. `prefix$(VAR)suffix` inside `<esi:assign>`.
    Interpolated(Vec<Element>),
    /// Dictionary literal: `{key: value, key: value}`.
    DictLiteral(Vec<(Expr, Expr)>),
    /// List literal: `[value, value, ...]`.
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
