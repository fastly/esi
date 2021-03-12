#[macro_use]
extern crate lazy_static;

use std::collections::HashMap;

use fancy_regex::{Captures, Regex};

lazy_static! {
    // Self-enclosed tags, such as <esi:comment text="Just write some HTML instead"/>
    static ref EMPTY_TAG_REGEX: Regex = Regex::new(r"(?si)\s*<esi:(?P<tag>[A-z]+)(?P<parameters>.*?)/>\s*").unwrap();

    // Tags with content, such as <esi:remove>test</esi:remove>
    static ref CONTENT_TAG_REGEX: Regex = Regex::new(r"(?si)\s*<esi:(?P<tag>[A-z]+)(?P<parameters>.*?)>(?P<content>.+)</esi:(?P=tag)+>\s*").unwrap();

    // Parameters, e.g. data="test"
    static ref PARAMETER_REGEX: Regex = Regex::new(r#"\s*(.+?)="(.*?)""#).unwrap();
}

pub struct Error {
    pub message: String,
}

impl Error {
    pub fn from_message(message: &str) -> Error {
        Error {
            message: String::from(message)
        }
    }
}

/// Handles requests to backends as part of the ESI execution process.
/// Implemented by `esi_fastly::FastlyRequestHandler`.
pub trait RequestHandler {
    /// Sends a request to the given URL and returns either an error or the response body.
    /// Returns response body.
    fn send_request(&self, url: &str) -> Result<String, Error>;
}

/// Processes a given ESI response body and returns the transformed body after all ESI instructions
/// have been executed.
pub fn transform_esi_string(mut body: String, client: &impl RequestHandler) -> Result<String, Error> {
    body = execute_content_tags(body, client)?;
    body = execute_empty_tags(body, client)?;

    println!("done.");

    Ok(body)
}

/// Representation of an ESI tag from a source response.
#[derive(Debug)]
pub struct Tag {
    name: String, // "include"
    content: Option<String>, // "hello world"
    parameters: HashMap<String, String> // src = "/a.html"
}

impl Tag {
    /// Parses an ESI tag from a regex capture.
    /// Uses named capture groups `tag`, `content`, and `parameters`.
    pub fn from_captures(cap: Captures) -> Tag {
        Tag {
            name: cap.name("tag").unwrap().as_str().to_string(),
            content: match cap.name("content") {
                Some(cont) => Some(cont.as_str().to_string()),
                None => None
            },
            parameters: Tag::parse_parameters(cap.name("parameters").unwrap().as_str())
        }
    }

    /// Parses XML-style attributes into a map.
    pub fn parse_parameters(input: &str) -> HashMap<String, String> {
        let mut map = HashMap::new();

        for cap in PARAMETER_REGEX.captures_iter(input) {
            match cap {
                Ok(cap) => {
                    map.insert(String::from(cap.get(1).unwrap().as_str()), String::from(cap.get(2).unwrap().as_str()));
                },
                _ => {}
            }
        }

        map
    }
}

fn send_request(src: &String, alt: Option<&String>, client: &impl RequestHandler) -> Result<String, Error> {
    match client.send_request(src) {
        Ok(resp) => Ok(resp),
        Err(err) => match alt {
            Some(alt) => match client.send_request(alt) {
                Ok(resp) => Ok(resp),
                Err(_) => Err(err)
            },
            None => Err(err)
        }
    }
}

fn execute_empty_tags(mut body: String, client: &impl RequestHandler) -> Result<String, Error> {
    let element = EMPTY_TAG_REGEX.find(&body).unwrap_or_default();

    match element {
        Some(element) => {
            let tag = Tag::from_captures(EMPTY_TAG_REGEX.captures(&body).unwrap().unwrap());

            println!("{:?}", tag);

            if tag.name == "include" {
                let src = match tag.parameters.get("src") {
                    Some(src) => src,
                    None => return Err(Error::from_message("No src parameter in <esi:include>"))
                };

                let alt = tag.parameters.get("alt");

                match send_request(src, alt, client) {
                    Ok(resp) => {
                        body = body.replace(element.as_str(), &resp);
                        execute_empty_tags(body, client)
                    },
                    Err(err) => {
                        match tag.parameters.get("onerror") {
                            Some(onerror) => {
                                if onerror == "continue" {
                                    println!("Failed to fetch {} but continued", src);
                                    body = body.replace(element.as_str(), "");
                                    execute_empty_tags(body, client)
                                } else {
                                    Err(err)
                                }
                            },
                            _ => Err(err)
                        }
                    }
                }
            } else if tag.name == "comment" {
                body = body.replace(element.as_str(), "");
                execute_empty_tags(body, client)
            } else {
                Err(Error::from_message(&format!("Unsupported tag: <esi:{}>", tag.name)))
            }
        },
        None => Ok(body)
    }
}

fn execute_content_tags(mut body: String, client: &impl RequestHandler) -> Result<String, Error> {
    let element = CONTENT_TAG_REGEX.find(&body).unwrap_or_default();

    match element {
        Some(element) => {
            let tag = Tag::from_captures(CONTENT_TAG_REGEX.captures(&body).unwrap().unwrap());

            println!("{:?}", tag);

            if tag.name == "remove" {
                body = body.replace(element.as_str(), "");
                execute_content_tags(body, client)
            } else {
                Err(Error::from_message(&format!("Unsupported tag: <esi:{}>", tag.name)))
            }
        },
        None => Ok(body)
    }}
