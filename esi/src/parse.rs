use crate::{ExecutionError, Result};
use log::debug;
use quick_xml::events::{BytesStart, Event as XmlEvent};
use quick_xml::name::QName;
use quick_xml::Reader;
use std::io::BufRead;
use std::ops::Deref;

// State carrier of Try branch
#[derive(Debug, PartialEq)]
enum TryTagArms {
    Try,
    Attempt,
    Except,
}

/// Representation of an ESI tag from a source response.
#[derive(Debug)]
pub struct Include {
    pub src: String,
    pub alt: Option<String>,
    pub continue_on_error: bool,
}

#[derive(Debug)]
pub enum Tag<'a> {
    Include {
        src: String,
        alt: Option<String>,
        continue_on_error: bool,
    },
    Try {
        attempt_events: Vec<Event<'a>>,
        except_events: Vec<Event<'a>>,
    },
    Assign {
        name: String,
        value: String,
    },
    Vars {
        name: Option<String>,
    },
}

/// Representation of either XML data or a parsed ESI tag.
#[derive(Debug)]
#[allow(clippy::upper_case_acronyms)]
pub enum Event<'e> {
    XML(XmlEvent<'e>),
    ESI(Tag<'e>),
}

// #[derive(Debug)]
struct TagNames {
    include: Vec<u8>,
    comment: Vec<u8>,
    remove: Vec<u8>,
    r#try: Vec<u8>,
    attempt: Vec<u8>,
    except: Vec<u8>,
    assign: Vec<u8>,
    vars: Vec<u8>,
}
impl TagNames {
    fn init(namespace: &str) -> Self {
        Self {
            include: format!("{namespace}:include",).into_bytes(),
            comment: format!("{namespace}:comment",).into_bytes(),
            remove: format!("{namespace}:remove",).into_bytes(),
            r#try: format!("{namespace}:try",).into_bytes(),
            attempt: format!("{namespace}:attempt",).into_bytes(),
            except: format!("{namespace}:except",).into_bytes(),
            assign: format!("{namespace}:assign",).into_bytes(),
            vars: format!("{namespace}:vars",).into_bytes(),
        }
    }
}

fn do_parse<'a, R>(
    reader: &mut Reader<R>,
    callback: &mut dyn FnMut(Event<'a>) -> Result<()>,
    task: &mut Vec<Event<'a>>,
    depth: &mut usize,
    current_arm: &mut Option<TryTagArms>,
    tag: &TagNames,
) -> Result<()>
where
    R: BufRead,
{
    let mut is_remove_tag = false;
    let mut open_include = false;
    let mut open_assign = false;
    let mut open_vars = false;

    let attempt_events = &mut Vec::new();
    let except_events = &mut Vec::new();

    let mut buffer = Vec::new();
    // Parse tags and build events vec
    loop {
        match reader.read_event_into(&mut buffer) {
            // Handle <esi:remove> tags
            Ok(XmlEvent::Start(e)) if e.name() == QName(&tag.remove) => {
                is_remove_tag = true;
            }

            Ok(XmlEvent::End(e)) if e.name() == QName(&tag.remove) => {
                if !is_remove_tag {
                    return unexpected_closing_tag_error(&e);
                }

                is_remove_tag = false;
            }
            _ if is_remove_tag => continue,

            // Handle <esi:include> tags, and ignore the contents if they are not self-closing
            Ok(XmlEvent::Empty(e)) if e.name().into_inner().starts_with(&tag.include) => {
                include_tag_handler(&e, callback, task, *depth)?;
            }

            Ok(XmlEvent::Start(e)) if e.name().into_inner().starts_with(&tag.include) => {
                open_include = true;
                include_tag_handler(&e, callback, task, *depth)?;
            }

            Ok(XmlEvent::End(e)) if e.name().into_inner().starts_with(&tag.include) => {
                if !open_include {
                    return unexpected_closing_tag_error(&e);
                }

                open_include = false;
            }

            _ if open_include => continue,

            // Ignore <esi:comment> tags
            Ok(XmlEvent::Empty(e)) if e.name().into_inner().starts_with(&tag.comment) => continue,

            // Handle <esi:try> tags
            Ok(XmlEvent::Start(ref e)) if e.name() == QName(&tag.r#try) => {
                *current_arm = Some(TryTagArms::Try);
                *depth += 1;
                continue;
            }

            // Handle <esi:attempt> and <esi:except> tags in recursion
            Ok(XmlEvent::Start(ref e))
                if e.name() == QName(&tag.attempt) || e.name() == QName(&tag.except) =>
            {
                if *current_arm != Some(TryTagArms::Try) {
                    return unexpected_opening_tag_error(e);
                }
                if e.name() == QName(&tag.attempt) {
                    *current_arm = Some(TryTagArms::Attempt);
                    do_parse(reader, callback, attempt_events, depth, current_arm, tag)?;
                } else if e.name() == QName(&tag.except) {
                    *current_arm = Some(TryTagArms::Except);
                    do_parse(reader, callback, except_events, depth, current_arm, tag)?;
                }
            }

            Ok(XmlEvent::End(ref e)) if e.name() == QName(&tag.r#try) => {
                *current_arm = None;
                if *depth == 0 {
                    return unexpected_closing_tag_error(e);
                }
                try_end_handler(*depth, task, attempt_events, except_events, callback)?;
                *depth -= 1;
                continue;
            }

            Ok(XmlEvent::End(ref e))
                if e.name() == QName(&tag.attempt) || e.name() == QName(&tag.except) =>
            {
                *current_arm = Some(TryTagArms::Try);
                if *depth == 0 {
                    return unexpected_closing_tag_error(e);
                }
                return Ok(());
            }

            // Handle <esi:assign> tags, and ignore the contents if they are not self-closing
            Ok(XmlEvent::Empty(e)) if e.name().into_inner().starts_with(&tag.assign) => {
                assign_tag_handler(&e, callback, task, *depth)?;
            }

            Ok(XmlEvent::Start(e)) if e.name().into_inner().starts_with(&tag.assign) => {
                open_assign = true;
                assign_tag_handler(&e, callback, task, *depth)?;
            }

            Ok(XmlEvent::End(e)) if e.name().into_inner().starts_with(&tag.assign) => {
                if !open_assign {
                    return unexpected_closing_tag_error(&e);
                }

                open_assign = false;
            }

            // Handle <esi:vars> tags
            Ok(XmlEvent::Empty(e)) if e.name().into_inner().starts_with(&tag.vars) => {
                vars_tag_handler(&e, callback, task, *depth)?;
            }

            Ok(XmlEvent::Start(e)) if e.name().into_inner().starts_with(&tag.vars) => {
                open_vars = true;
                vars_tag_handler(&e, callback, task, *depth)?;
            }

            Ok(XmlEvent::End(e)) if e.name().into_inner().starts_with(&tag.vars) => {
                if !open_vars {
                    return unexpected_closing_tag_error(&e);
                }

                open_vars = false;
            }

            Ok(XmlEvent::Eof) => {
                debug!("End of document");
                break;
            }
            Ok(e) => {
                if *depth == 0 {
                    callback(Event::XML(e.into_owned()))?;
                } else {
                    task.push(Event::XML(e.into_owned()));
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Parses the ESI document from the given `reader` and calls the `callback` closure upon each successfully parsed ESI tag.
pub fn parse_tags<'a, R>(
    namespace: &str,
    reader: &mut Reader<R>,
    callback: &mut dyn FnMut(Event<'a>) -> Result<()>,
) -> Result<()>
where
    R: BufRead,
{
    debug!("Parsing document...");

    // Initialize the ESI tags
    let tags = TagNames::init(namespace);
    // set the initial depth of nested tags
    let mut depth = 0;
    let mut root = Vec::new();

    let mut current_arm: Option<TryTagArms> = None;

    do_parse(
        reader,
        callback,
        &mut root,
        &mut depth,
        &mut current_arm,
        &tags,
    )?;
    debug!("Root: {:?}", root);

    Ok(())
}

fn parse_include<'a>(elem: &BytesStart) -> Result<Tag<'a>> {
    let src = match elem
        .attributes()
        .flatten()
        .find(|attr| attr.key.into_inner() == b"src")
    {
        Some(attr) => String::from_utf8(attr.value.to_vec()).unwrap(),
        None => {
            return Err(ExecutionError::MissingRequiredParameter(
                String::from_utf8(elem.name().into_inner().to_vec()).unwrap(),
                "src".to_string(),
            ));
        }
    };

    let alt = elem
        .attributes()
        .flatten()
        .find(|attr| attr.key.into_inner() == b"alt")
        .map(|attr| String::from_utf8(attr.value.to_vec()).unwrap());

    let continue_on_error = elem
        .attributes()
        .flatten()
        .find(|attr| attr.key.into_inner() == b"onerror")
        .is_some_and(|attr| &attr.value.to_vec() == b"continue");

    Ok(Tag::Include {
        src,
        alt,
        continue_on_error,
    })
}

fn parse_assign<'a>(elem: &BytesStart) -> Result<Tag<'a>> {
    let name = match elem
        .attributes()
        .flatten()
        .find(|attr| attr.key.into_inner() == b"name")
    {
        Some(attr) => String::from_utf8(attr.value.to_vec()).unwrap(),
        None => {
            return Err(ExecutionError::MissingRequiredParameter(
                String::from_utf8(elem.name().into_inner().to_vec()).unwrap(),
                "name".to_string(),
            ));
        }
    };

    let value = match elem
        .attributes()
        .flatten()
        .find(|attr| attr.key.into_inner() == b"value")
    {
        Some(attr) => String::from_utf8(attr.value.to_vec()).unwrap(),
        None => {
            return Err(ExecutionError::MissingRequiredParameter(
                String::from_utf8(elem.name().into_inner().to_vec()).unwrap(),
                "value".to_string(),
            ));
        }
    };

    Ok(Tag::Assign { name, value })
}

fn parse_vars<'a>(elem: &BytesStart) -> Result<Tag<'a>> {
    let name = elem
        .attributes()
        .flatten()
        .find(|attr| attr.key.into_inner() == b"name")
        .map(|attr| String::from_utf8(attr.value.to_vec()).unwrap());

    Ok(Tag::Vars { name })
}

// Helper function to handle the end of a <esi:try> tag
// If the depth is 1, the `callback` closure is called with the `Tag::Try` event
// Otherwise, a new `Tag::Try` event is pushed to the `task` vector
fn try_end_handler<'a>(
    depth: usize,
    task: &mut Vec<Event<'a>>,
    attempt_events: &mut Vec<Event<'a>>,
    except_events: &mut Vec<Event<'a>>,
    callback: &mut dyn FnMut(Event<'a>) -> Result<()>,
) -> Result<()> {
    if depth == 1 {
        callback(Event::ESI(Tag::Try {
            attempt_events: std::mem::take(attempt_events),
            except_events: std::mem::take(except_events),
        }))?;
    } else {
        task.push(Event::ESI(Tag::Try {
            attempt_events: std::mem::take(attempt_events),
            except_events: std::mem::take(except_events),
        }));
    }

    Ok(())
}

// Helper function to handle <esi:include> tags
// If the depth is 0, the `callback` closure is called with the `Tag::Include` event
// Otherwise, a new `Tag::Include` event is pushed to the `task` vector
fn include_tag_handler<'e>(
    elem: &BytesStart,
    callback: &mut dyn FnMut(Event<'e>) -> Result<()>,
    task: &mut Vec<Event<'e>>,
    depth: usize,
) -> Result<()> {
    if depth == 0 {
        callback(Event::ESI(parse_include(elem)?))?;
    } else {
        task.push(Event::ESI(parse_include(elem)?));
    }

    Ok(())
}

// Helper function to handle <esi:assign> tags
// If the depth is 0, the `callback` closure is called with the `Tag::Assign` event
// Otherwise, a new `Tag::Assign` event is pushed to the `task` vector
fn assign_tag_handler<'e>(
    elem: &BytesStart,
    callback: &mut dyn FnMut(Event<'e>) -> Result<()>,
    task: &mut Vec<Event<'e>>,
    depth: usize,
) -> Result<()> {
    if depth == 0 {
        callback(Event::ESI(parse_assign(elem)?))?;
    } else {
        task.push(Event::ESI(parse_assign(elem)?));
    }

    Ok(())
}

// Helper function to handle <esi:vars> tags
// If the depth is 0, the `callback` closure is called with the `Tag::Assign` event
// Otherwise, a new `Tag::Vars` event is pushed to the `task` vector
fn vars_tag_handler<'e>(
    elem: &BytesStart,
    callback: &mut dyn FnMut(Event<'e>) -> Result<()>,
    task: &mut Vec<Event<'e>>,
    depth: usize,
) -> Result<()> {
    if depth == 0 {
        callback(Event::ESI(parse_vars(elem)?))?;
    } else {
        task.push(Event::ESI(parse_vars(elem)?));
    }

    Ok(())
}

// Helper function return UnexpectedClosingTag error
fn unexpected_closing_tag_error<T>(e: &T) -> Result<()>
where
    T: Deref<Target = [u8]>,
{
    Err(ExecutionError::UnexpectedClosingTag(
        String::from_utf8_lossy(e).to_string(),
    ))
}

// Helper function return UnexpectedClosingTag error
fn unexpected_opening_tag_error<T>(e: &T) -> Result<()>
where
    T: Deref<Target = [u8]>,
{
    Err(ExecutionError::UnexpectedOpeningTag(
        String::from_utf8_lossy(e).to_string(),
    ))
}
