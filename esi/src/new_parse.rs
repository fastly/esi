use nom::branch::alt;
use nom::bytes::streaming::*;
use nom::character::streaming::*;
use nom::combinator::{complete, map, not, peek, recognize, success, verify};
use nom::error::{Error, ParseError};
use nom::multi::{fold_many0, length_data, many0, many_till};
use nom::sequence::{delimited, pair, preceded, separated_pair, tuple};
use nom::{IResult, Parser};

#[derive(Debug)]
enum Chunk<'a> {
    EsiStartTag(&'a str, Vec<(&'a str, &'a str)>),
    EsiEndTag(&'a str),
    Text(&'a str),
}

fn parse(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    fold_many0(
        complete(chunk),
        Vec::new,
        |mut acc: Vec<Chunk>, mut item| {
            acc.append(&mut item);
            acc
        },
    )(input)
}

fn chunk(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    alt((text, esi_tag, html))(input)
}

fn esi_tag(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    alt((esi_start_tag, esi_end_tag))(input)
}
fn esi_start_tag(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        delimited(tag("<esi:"), pair(esi_tag_name, attributes), char('>')),
        |(tagname, attrs)| vec![Chunk::EsiStartTag(tagname, attrs)],
    )(input)
}
fn esi_end_tag(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        delimited(tag("</esi:"), is_not(">"), char('>')),
        |s: &str| vec![Chunk::EsiEndTag(s)],
    )(input)
}

fn esi_tag_name(input: &str) -> IResult<&str, &str, Error<&str>> {
    tag("vars")(input)
}

fn attributes(input: &str) -> IResult<&str, Vec<(&str, &str)>, Error<&str>> {
    many0(separated_pair(
        preceded(multispace1, alpha1),
        char('='),
        xmlstring,
    ))(input)
}

fn xmlstring(input: &str) -> IResult<&str, &str, Error<&str>> {
    delimited(char('"'), is_not("\""), char('"'))(input) // TODO: obviously wrong
}

fn html(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    alt((script, end_tag, start_tag))(input)
}

fn script(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        tuple((
            recognize(verify(
                delimited(tag_no_case("<script"), attributes, char('>')),
                |attrs: &Vec<(&str, &str)>| !attrs.iter().any(|(k, _)| k == &"src"),
            )),
            length_data(map(
                peek(many_till(anychar, tag_no_case("</script"))),
                |(v, _)| v.len(),
            )),
            recognize(delimited(
                tag_no_case("</script"),
                alt((is_not(">"), success(""))),
                char('>'),
            )),
        )),
        |(start, script, end)| {
            println!("script parser succeeded");
            vec![Chunk::Text(start), Chunk::Text(script), Chunk::Text(end)]
        },
    )(input)
}

fn end_tag(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        recognize(delimited(tag("</"), is_not(">"), char('>'))),
        |s: &str| vec![Chunk::Text(s)],
    )(input)
}

fn start_tag(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        recognize(delimited(char('<'), is_not(">"), char('>'))),
        |s: &str| vec![Chunk::Text(s)],
    )(input)
}
fn text(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(take_until1("<"), |s: &str| vec![Chunk::Text(s)])(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_parse() {
        let x = parse(
            "<a>foo</a><bar />baz<esi:vars name=\"$hello\"><sCripT src=\"whatever\"><baz><script> less < more </script>",
        );
        println!("{:?}", x);
    }
    #[test]
    fn test_new_parse_script() {
        let x = script("<sCripT> less < more </scRIpt>");
        println!("{:?}", x);
    }
    #[test]
    fn test_new_parse_script_with_src() {
        let x = parse("<sCripT src=\"whatever\">");
        println!("{:?}", x);
    }
    #[test]
    fn test_new_parse_esi_tag() {
        let x = esi_start_tag("<esi:vars foo=\"hello\">");
        println!("{:?}", x);
    }
}
