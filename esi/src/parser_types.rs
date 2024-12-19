#[derive(Debug, Clone)]
pub enum Tag<'a> {
    Include(Vec<(&'a str, &'a str)>),
    Choose(Vec<Chunk<'a>>, Option<Vec<Chunk<'a>>>),
    When(Vec<(&'a str, &'a str)>, Vec<Chunk<'a>>),
    Otherwise(Vec<Chunk<'a>>),
    Try(Vec<Vec<Chunk<'a>>>, Option<Vec<Chunk<'a>>>),
    Attempt(Vec<Chunk<'a>>),
    Except(Vec<Chunk<'a>>),
    Assign(Vec<(&'a str, &'a str)>, Option<Vec<Chunk<'a>>>),
}

#[derive(Debug, Clone)]
pub enum Chunk<'a> {
    Esi(Tag<'a>),
    Expr(&'a str),
    Html(&'a str),
    Text(&'a str),
}
