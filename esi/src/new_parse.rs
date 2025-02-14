use nom::branch::alt;
use nom::bytes::complete::is_not as complete_is_not;
use nom::bytes::streaming::*;
use nom::character::streaming::*;
use nom::combinator::{complete, map, map_res, opt, peek, recognize, success, verify};
use nom::error::Error;
use nom::multi::{fold_many0, length_data, many0, many1, many_till, separated_list0};
use nom::sequence::{delimited, preceded, separated_pair, terminated, tuple};
use nom::Finish;
use nom::{AsChar, IResult};

use crate::parser_types::*;

pub fn parse_document(input: &str) -> Result<Ast, Error<&str>> {
    let (_, o) = parse(input).finish()?;
    Ok(Ast(o))
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
    alt((interpolated_text, interpolated_expression, esi_tag, html))(input)
}

fn esi_tag(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    alt((
        esi_vars,
        esi_comment,
        esi_remove,
        esi_text,
        esi_include,
        esi_choose,
        esi_when,
        esi_otherwise,
        esi_attempt,
        esi_except,
        esi_try,
        esi_assign,
    ))(input)
}

fn esi_assign(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    alt((esi_assign_short, esi_assign_long))(input)
}

fn esi_assign_short(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        delimited(
            tag("<esi:assign"),
            attributes,
            preceded(multispace0, alt((tag(">"), tag("/>")))),
        ),
        |attrs| vec![Chunk::Esi(Tag::Assign(attrs, None))],
    )(input)
}

fn esi_assign_long(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        tuple((
            delimited(
                tag("<esi:assign"),
                attributes,
                preceded(multispace0, alt((tag(">"), tag("/>")))),
            ),
            parse_interpolated,
            tag("</esi:assign>"),
        )),
        |(attrs, chunks, _)| vec![Chunk::Esi(Tag::Assign(attrs, Some(chunks)))],
    )(input)
}
fn esi_except(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        delimited(
            tag("<esi:except>"),
            parse_interpolated,
            tag("</esi:except>"),
        ),
        |v| vec![Chunk::Esi(Tag::Except(v))],
    )(input)
}
fn esi_attempt(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        delimited(
            tag("<esi:attempt>"),
            parse_interpolated,
            tag("</esi:attempt>"),
        ),
        |v| vec![Chunk::Esi(Tag::Attempt(v))],
    )(input)
}
fn esi_try(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(delimited(tag("<esi:try>"), parse, tag("</esi:try>")), |v| {
        let mut attempts = vec![];
        let mut except = None;
        for chunk in v {
            match chunk {
                Chunk::Esi(Tag::Attempt(cs)) => attempts.push(cs),
                Chunk::Esi(Tag::Except(cs)) => {
                    except = Some(cs);
                }
                _ => {}
            }
        }
        vec![Chunk::Esi(Tag::Try(attempts, except))]
    })(input)
}

fn esi_otherwise(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        delimited(
            tag("<esi:otherwise>"),
            parse_interpolated,
            tag("</esi:otherwise>"),
        ),
        |v| vec![Chunk::Esi(Tag::Otherwise(v))],
    )(input)
}

fn esi_when(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        tuple((
            delimited(
                tag("<esi:when"),
                attributes,
                preceded(multispace0, alt((tag(">"), tag("/>")))),
            ),
            parse_interpolated,
            tag("</esi:when>"),
        )),
        |(attrs, contents, _)| {
            // TODO: matchname field (and any others)
            if let Some((_k, v)) = attrs.iter().find(|(k, _v)| *k == "test") {
                if let Ok((_, expr)) = expr(v) {
                    vec![Chunk::Esi(Tag::When(expr, contents))]
                } else {
                    // Expression doesn't parse, will never trigger
                    vec![]
                }
            } else {
                // No test field. Will never trigger.
                vec![]
            }
        },
    )(input)
}

fn esi_choose(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        delimited(tag("<esi:choose>"), parse, tag("</esi:choose>")),
        |v| {
            let mut whens = vec![];
            let mut otherwise = None;
            for chunk in v {
                match chunk {
                    Chunk::Esi(Tag::When(..)) => whens.push(chunk),
                    Chunk::Esi(Tag::Otherwise(cs)) => {
                        otherwise = Some(cs);
                    }
                    _ => {}
                }
            }
            vec![Chunk::Esi(Tag::Choose(whens, otherwise))]
        },
    )(input)
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
            if let Some((_k, v)) = attrs.iter().find(|(k, _v)| *k == "name") {
                if let Ok((_, expr)) = expression(v) {
                    Ok(expr)
                } else {
                    Err("failed to parse expression")
                }
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

fn esi_comment(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        delimited(
            tag("<esi:comment"),
            attributes,
            preceded(multispace0, alt((tag(">"), tag("/>")))),
        ),
        |_| vec![],
    )(input)
}
fn esi_remove(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        delimited(tag("<esi:remove>"), parse, tag("</esi:remove>")),
        |_| vec![],
    )(input)
}

fn esi_text(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        tuple((
            tag("<esi:text>"),
            length_data(map(
                peek(many_till(anychar, tag("</esi:text>"))),
                |(v, _)| v.len(),
            )),
            tag("</esi:text>"),
        )),
        |(_, v, _)| vec![Chunk::Text(v)],
    )(input)
}
fn esi_include(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(
        delimited(
            tag("<esi:include"),
            attributes,
            preceded(multispace0, alt((tag(">"), tag("/>")))),
        ),
        |attrs| vec![Chunk::Esi(Tag::Include(attrs))],
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
        |(start, script, end)| vec![Chunk::Html(start), Chunk::Text(script), Chunk::Html(end)],
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

fn is_alphanumeric_or_underscore(c: char) -> bool {
    c.is_alphanum() || c == '_'
}

fn is_lower_alphanumeric_or_underscore(c: char) -> bool {
    c.is_ascii_lowercase() || c.is_numeric() || c == '_'
}

fn fn_name(input: &str) -> IResult<&str, &str, Error<&str>> {
    preceded(char('$'), take_while1(is_lower_alphanumeric_or_underscore))(input)
}

fn var_name(input: &str) -> IResult<&str, (&str, Option<&str>, Option<Expr>), Error<&str>> {
    tuple((
        take_while1(is_alphanumeric_or_underscore),
        opt(delimited(char('{'), var_key, char('}'))),
        opt(preceded(char('|'), fn_nested_argument)),
    ))(input)
}

fn not_dollar_or_curlies(input: &str) -> IResult<&str, &str, Error<&str>> {
    take_till(|c: char| "${},\"".contains(c))(input)
}

// TODO: handle escaping
fn single_quoted_string(input: &str) -> IResult<&str, &str, Error<&str>> {
    delimited(
        char('\''),
        take_till(|c: char| c == '\'' || !c.is_ascii()),
        char('\''),
    )(input)
}
fn triple_quoted_string(input: &str) -> IResult<&str, &str, Error<&str>> {
    delimited(
        tag("'''"),
        length_data(map(peek(many_till(anychar, tag("'''"))), |(v, _)| v.len())),
        tag("'''"),
    )(input)
}

fn string(input: &str) -> IResult<&str, Expr, Error<&str>> {
    map(
        alt((single_quoted_string, triple_quoted_string)),
        |string| {
            if string.is_empty() {
                Expr::String(None)
            } else {
                Expr::String(Some(string))
            }
        },
    )(input)
}

fn var_key(input: &str) -> IResult<&str, &str, Error<&str>> {
    alt((
        single_quoted_string,
        triple_quoted_string,
        not_dollar_or_curlies,
    ))(input)
}

fn fn_argument(input: &str) -> IResult<&str, Vec<Expr>, Error<&str>> {
    let (input, mut parsed) = separated_list0(
        tuple((multispace0, char(','), multispace0)),
        fn_nested_argument,
    )(input)?;

    // If the parsed list contains a single empty string element return an empty vec
    if parsed.len() == 1 && parsed[0] == Expr::String(None) {
        parsed = vec![];
    }
    Ok((input, parsed))
}

fn fn_nested_argument(input: &str) -> IResult<&str, Expr, Error<&str>> {
    alt((call, variable, string))(input)
}

fn call(input: &str) -> IResult<&str, Expr, Error<&str>> {
    let (input, parsed) = tuple((
        fn_name,
        delimited(
            terminated(char('('), multispace0),
            fn_argument,
            preceded(multispace0, char(')')),
        ),
    ))(input)?;

    let (name, args) = parsed;

    Ok((input, Expr::Call(name, args)))
}

fn variable(input: &str) -> IResult<&str, Expr, Error<&str>> {
    let (input, parsed) = delimited(tag("$("), var_name, char(')'))(input)?;

    let (name, key, default) = parsed;
    let default = default.map(Box::new);

    Ok((input, Expr::Variable(name, key, default)))
}

fn operator(input: &str) -> IResult<&str, Operator, Error<&str>> {
    map(
        alt((tag("matches"), tag("matches_i"))),
        |opstr| match opstr {
            "matches" => Operator::Matches,
            "matches_i" => Operator::MatchesInsensitive,
            _ => unreachable!(),
        },
    )(input)
}

fn interpolated_expression(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(alt((call, variable)), |expr| vec![Chunk::Expr(expr)])(input)
}

fn expr(input: &str) -> IResult<&str, Expr, Error<&str>> {
    let (rest, exp) = alt((call, variable, string))(input)?;

    if let Ok((rest, (operator, right_exp))) =
        tuple((delimited(multispace1, operator, multispace1), expr))(rest)
    {
        Ok((
            rest,
            Expr::Comparison {
                left: Box::new(exp),
                operator: operator,
                right: Box::new(right_exp),
            },
        ))
    } else {
        Ok((rest, exp))
    }
}
fn expression(input: &str) -> IResult<&str, Vec<Chunk>, Error<&str>> {
    map(expr, |x| vec![Chunk::Expr(x)])(input)
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
<esi:vars name="$(hello)">
<esi:vars>
hello <br>
</esi:vars>
<sCripT src="whatever">
<baz>
<script> less < more </script>
<esi:remove>should not appear</esi:remove>
<esi:comment text="also should not appear" />
<esi:text> this <esi:vars>$(should)</esi> appear unchanged</esi:text>
<esi:include src="whatever" />
<esi:choose>
should not appear
</esi:choose>
<esi:choose>
should not appear
<esi:when test="whatever">hi</esi:when>
<esi:otherwise>goodbye</esi:otherwise>
should not appear
</esi:choose>
<esi:try>
should not appear
<esi:attempt>
attempt 1
</esi:attempt>
should not appear
<esi:attempt>
attempt 2
</esi:attempt>
should not appear
<esi:except>
exception!
</esi:except>
</esi:try>"#;
        let (rest, _) = parse(input).unwrap();
        // Just test to make sure it parsed the whole thing
        assert_eq!(rest.len(), 0);
    }
    #[test]
    fn test_new_parse_script() {
        let (rest, x) = script("<sCripT> less < more </scRIpt>").unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(
            x,
            [
                Chunk::Html("<sCripT>"),
                Chunk::Text(" less < more "),
                Chunk::Html("</scRIpt>")
            ]
        );
    }
    #[test]
    fn test_new_parse_script_with_src() {
        let (rest, x) = parse("<sCripT src=\"whatever\">").unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(x, [Chunk::Html("<sCripT src=\"whatever\">")]);
    }
    #[test]
    fn test_new_parse_esi_vars_short() {
        let (rest, x) = esi_tag(r#"<esi:vars name="$(hello)">"#).unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(x, [Chunk::Expr(Expr::Variable("hello", None, None)),]);
    }
    #[test]
    fn test_new_parse_esi_vars_long() {
        let (rest, x) = parse(
            r#"<esi:vars>hello<esi:vars><br></esi:vars><esi:vars name="$(bleh)" />there</esi:vars>"#,
        ).unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(
            x,
            [
                Chunk::Text("hello"),
                Chunk::Html("<br>"),
                Chunk::Expr(Expr::Variable("bleh", None, None)),
                Chunk::Text("there")
            ]
        );
    }
    #[test]
    fn test_new_parse_complex_expr() {
        let (rest, x) = parse(r#"<esi:vars name="$call('hello') matches $(var{'key'})">"#).unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(
            x,
            [Chunk::Expr(Expr::Comparison {
                left: Box::new(Expr::Call("call", vec![Expr::String(Some("hello"))])),
                operator: Operator::Matches,
                right: Box::new(Expr::Variable("var", Some("key"), None))
            })]
        );
    }

    #[test]
    fn test_new_parse_plain_text() {
        let (rest, x) = parse("hello\nthere").unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(x, [Chunk::Text("hello\nthere")]);
    }
    #[test]
    fn test_new_parse_interpolated() {
        let (rest, x) = parse("hello $(foo)<esi:vars>goodbye $(foo)</esi:vars>").unwrap();
        assert_eq!(rest.len(), 0);
        assert_eq!(
            x,
            [
                Chunk::Text("hello $(foo)"),
                Chunk::Text("goodbye "),
                Chunk::Expr(Expr::Variable("foo", None, None)),
            ]
        );
    }
    #[test]
    fn test_new_parse_examples() {
        let (rest, _) = parse(include_str!(
            "../../examples/esi_vars_example/src/index.html"
        ))
        .unwrap();
        // just make sure it parsed the whole thing
        assert_eq!(rest.len(), 0);
    }
}
