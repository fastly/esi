#[derive(Debug, PartialEq, Clone)]
pub enum Tag<'a> {
    Include {
        src: String,
        alt: Option<String>,
        continue_on_error: bool,
    },
    Try {
        attempt_events: Vec<Chunk<'a>>,
        except_events: Vec<Chunk<'a>>,
    },
    Assign {
        name: String,
        value: String,
    },
    Vars {
        name: Option<String>,
    },
    When {
        test: String,
        match_name: Option<String>,
    },
    Choose {
        when_branches: Vec<(Tag<'a>, Vec<Chunk<'a>>)>,
        otherwise_events: Vec<Chunk<'a>>,
    },
    Attempt(Vec<Chunk<'a>>),
    Except(Vec<Chunk<'a>>),
    Otherwise,  // Changed to unit variant like When - content follows as separate chunks
}

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
    Variable(&'a str, Option<Box<Expr<'a>>>, Option<Box<Expr<'a>>>),
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
