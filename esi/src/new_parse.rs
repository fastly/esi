use nom::branch::alt;
use nom::bytes::complete::is_not as complete_is_not;
use nom::bytes::streaming::*;
use nom::character::streaming::*;
use nom::combinator::{complete, map, map_res, not, peek, recognize, success, verify};
use nom::error::{Error, ParseError};
use nom::multi::{fold_many0, length_data, length_value, many0, many1, many_till};
use nom::sequence::{delimited, pair, preceded, separated_pair, tuple};
use nom::{IResult, Parser};

use crate::parser_types::*;

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

fn parse_interpolated(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    fold_many0(
        complete(interpolated_chunk),
        Vec::new,
        |mut acc: Vec<Chunk>, mut item| {
            acc.append(&mut item);
            acc
        },
    )(input)
}

fn interpolated_chunk(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    alt((interpolated_text, interpolation, esi_tag, html))(input)
}

fn esi_tag(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    alt((esi_vars,))(input)
}

fn esi_vars(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    alt((esi_vars_short, esi_vars_long))(input)
}

fn esi_vars_short(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map_res(
        delimited(
            tag("<esi:vars"),
            attributes,
            preceded(multispace0, alt((tag(">"), tag("/>")))),
        ),
        |attrs| {
            if let Some((k, v)) = attrs.iter().find(|(k, v)| *k == "name") {
                Ok(vec![Chunk::Expr(v)])
            } else {
                Err("no name field in short form vars")
            }
        },
    )(input)
}

fn esi_vars_long(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        delimited(tag("<esi:vars>"), parse_interpolated, tag("</esi:vars>")),
        |v| v,
    )(input)
}

fn attributes(input: &str) -> IResult<&str, Vec<(&str, &str)>, Error<&str>> {
    many0(separated_pair(
        preceded(multispace1, alpha1),
        char('='),
        htmlstring,
    ))(input)
}

fn htmlstring(input: &str) -> IResult<&str, &str, Error<&str>> {
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
            vec![Chunk::Html(start), Chunk::Text(script), Chunk::Html(end)]
        },
    )(input)
}

fn end_tag(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        verify(
            recognize(delimited(tag("</"), is_not(">"), char('>'))),
            |s: &str| !s.starts_with("</esi:"),
        ),
        |s: &str| vec![Chunk::Html(s)],
    )(input)
}

fn start_tag(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        verify(
            recognize(delimited(char('<'), is_not(">"), char('>'))),
            |s: &str| !s.starts_with("</") && !s.starts_with("<esi:"),
        ),
        |s: &str| vec![Chunk::Html(s)],
    )(input)
}
fn text(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(recognize(many1(complete_is_not("<"))), |s: &str| {
        vec![Chunk::Text(s)]
    })(input)
}
fn interpolated_text(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(recognize(many1(complete_is_not("<$"))), |s: &str| {
        vec![Chunk::Text(s)]
    })(input)
}
fn interpolation(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        recognize(delimited(tag("$("), is_not(")"), tag(")"))),
        |s: &str| vec![Chunk::Expr(s)],
    )(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_parse() {
        let input = r#"
<a>foo</a>
<bar />
baz
<esi:vars name="$hello">
<esi:vars>
hello <br>
</esi:vars>
<sCripT src="whatever">
<baz>
<script> less < more </script>"#;
        let output = parse(input);
        println!("{input}");
        println!("{:?}", output);
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
    fn test_new_parse_esi_vars_short() {
        let x = esi_tag(r#"<esi:vars name="hello">"#);
        println!("{:?}", x);
    }
    #[test]
    fn test_new_parse_esi_vars_long() {
        let x = esi_tag(
            r#"<esi:vars>hello<esi:vars><br></esi:vars><esi:vars name="bleh" />there</esi:vars>"#,
        );
        println!("{:?}", x);
    }
    #[test]
    fn test_new_parse_plain_text() {
        let x = parse("hello\nthere");
        println!("{:?}", x);
    }
    #[test]
    fn test_new_parse_esi_end_tag() {
        let x = parse("</esi:vars>");
        println!("{:?}", x);
    }
    #[test]
    fn test_new_parse_interpolated() {
        let x = parse("hello $(foo)<esi:vars>goodbye $(foo)</esi:vars>");
        println!("{:?}", x);
    }
}
