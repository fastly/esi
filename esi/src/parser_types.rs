#[derive(Debug)]
pub enum Tag {
    Vars,
    Include,
    Text,
    Choose,
    When,
    Otherwise,
    Try,
    Attempt,
    Except,
}

#[derive(Debug)]
pub enum Chunk<'a> {
    EsiStartTag(Tag, Vec<(&'a str, &'a str)>),
    EsiEndTag(Tag),
    Expr(&'a str),
    Html(&'a str),
    Text(&'a str),
}
