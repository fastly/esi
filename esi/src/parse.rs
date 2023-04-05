use crate::{ExecutionError, Result};
use log::debug;
use quick_xml::events::BytesStart;
use quick_xml::Reader;
use std::io::BufRead;

/// Representation of an ESI tag from a source response.
#[derive(Debug)]
pub enum Tag {
    Include {
        src: String,
        alt: Option<String>,
        continue_on_error: bool,
    },
}

/// Representation of either XML data or a parsed ESI tag.
#[derive(Debug)]
#[allow(clippy::upper_case_acronyms)]
pub enum Event<'e> {
    XML(quick_xml::events::Event<'e>),
    ESI(Tag),
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

    let mut remove = false;
    let mut open_include = false;

    let esi_include = format!("{}:include", namespace).into_bytes();
    let esi_comment = format!("{}:comment", namespace).into_bytes();
    let esi_remove = format!("{}:remove", namespace).into_bytes();

    let mut buffer = Vec::new();
    // Parse tags and build events vec
    loop {
        match reader.read_event_into(&mut buffer) {
            // Handle <esi:remove> tags
            Ok(quick_xml::events::Event::Start(elem)) if elem.starts_with(&esi_remove) => {
                remove = true;
            }
            Ok(quick_xml::events::Event::End(elem)) if elem.starts_with(&esi_remove) => {
                if !remove {
                    return Err(ExecutionError::UnexpectedClosingTag(
                        String::from_utf8(elem.to_vec()).unwrap(),
                    ));
                }

                remove = false;
            }
            _ if remove => continue,

            // Handle <esi:include> tags, and ignore the contents if they are not self-closing
            Ok(quick_xml::events::Event::Empty(elem))
                if elem.name().into_inner().starts_with(&esi_include) =>
            {
                callback(parse_include(&elem)?)?;
            }

            Ok(quick_xml::events::Event::Start(elem))
                if elem.name().into_inner().starts_with(&esi_include) =>
            {
                open_include = true;
                callback(parse_include(&elem)?)?;
            }

            Ok(quick_xml::events::Event::End(elem))
                if elem.name().into_inner().starts_with(&esi_include) =>
            {
                if !open_include {
                    return Err(ExecutionError::UnexpectedClosingTag(
                        String::from_utf8(elem.to_vec()).unwrap(),
                    ));
                }

                open_include = false;
            }

            _ if open_include => continue,

            // Ignore <esi:comment> tags
            Ok(quick_xml::events::Event::Empty(elem))
                if elem.name().into_inner().starts_with(&esi_comment) =>
            {
                continue
            }

            Ok(quick_xml::events::Event::Eof) => {
                debug!("End of document");
                break;
            }
            Ok(e) => callback(Event::XML(e.into_owned()))?,
            _ => {}
        }
    }

    Ok(())
}

fn parse_include<'a, 'b>(elem: &'a BytesStart) -> Result<Event<'b>> {
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
        .map(|attr| &attr.value.to_vec() == b"continue")
        == Some(true);

    Ok(Event::ESI(Tag::Include {
        src,
        alt,
        continue_on_error,
    }))
}
