//! Tests for DCA (Dynamic Content Assembly) configuration features:
//! - `default_dca`: global default DCA mode
//! - `max_include_depth`: nesting depth limit
//! - `Edge-Control` header parsing (via `enable_edge_control`)
//! - `inherit_parent_dca`: subtree DCA inheritance

use esi::{Configuration, DcaMode, Processor};
use fastly::{Request, Response};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

// ---------------------------------------------------------------------------
// Helper: run ESI processing with a config + dispatcher, return output string
// ---------------------------------------------------------------------------

fn run<F>(input: &str, config: Configuration, dispatcher: &F) -> esi::Result<String>
where
    F: Fn(Request, Option<u32>) -> esi::Result<esi::PendingFragmentContent> + 'static,
{
    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(None, config);
    processor.process_stream(
        reader,
        &mut output,
        Some(
            dispatcher as &dyn Fn(Request, Option<u32>) -> esi::Result<esi::PendingFragmentContent>,
        ),
        None,
    )?;
    Ok(String::from_utf8(output).unwrap())
}

fn static_body(
    body: &'static str,
) -> impl Fn(Request, Option<u32>) -> esi::Result<esi::PendingFragmentContent> {
    move |_req, _maxwait| {
        Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
            Response::from_body(body),
        )))
    }
}

fn with_edge_control(
    body: &'static str,
    header: &'static str,
) -> impl Fn(Request, Option<u32>) -> esi::Result<esi::PendingFragmentContent> {
    move |_req, _maxwait| {
        let mut resp = Response::from_body(body);
        resp.set_header("Edge-Control", header);
        Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
            resp,
        )))
    }
}

// ===========================================================================
// 1. default_dca tests
// ===========================================================================

/// With default_dca=None (the default), include without dca attr inserts raw content.
#[test]
fn test_default_dca_none_includes_raw() -> esi::Result<()> {
    let d = static_body(r#"<esi:assign name="x" value="1"/><esi:vars>$(x)</esi:vars>"#);
    let result = run(
        r#"<esi:include src="http://example.com/frag"/>"#,
        Configuration::default(),
        &d,
    )?;
    assert_eq!(
        result,
        r#"<esi:assign name="x" value="1"/><esi:vars>$(x)</esi:vars>"#
    );
    Ok(())
}

/// With default_dca=Esi, include without dca attr processes content as ESI.
#[test]
fn test_default_dca_esi_processes_content() -> esi::Result<()> {
    let d = static_body(r#"<esi:assign name="x" value="42"/><esi:vars>X is $(x)</esi:vars>"#);
    let result = run(
        r#"<esi:include src="http://example.com/frag"/>"#,
        Configuration::default().with_default_dca(DcaMode::Esi),
        &d,
    )?;
    assert_eq!(result, "X is 42");
    Ok(())
}

/// Explicit dca="none" on tag overrides default_dca=Esi.
#[test]
fn test_explicit_dca_none_overrides_default_esi() -> esi::Result<()> {
    let d = static_body(r#"<esi:assign name="x" value="1"/><esi:vars>$(x)</esi:vars>"#);
    let result = run(
        r#"<esi:include src="http://example.com/frag" dca="none"/>"#,
        Configuration::default().with_default_dca(DcaMode::Esi),
        &d,
    )?;
    assert_eq!(
        result,
        r#"<esi:assign name="x" value="1"/><esi:vars>$(x)</esi:vars>"#
    );
    Ok(())
}

/// Explicit dca="esi" on tag overrides default_dca=None.
#[test]
fn test_explicit_dca_esi_overrides_default_none() -> esi::Result<()> {
    let d = static_body(r#"<esi:assign name="y" value="99"/><esi:vars>Y is $(y)</esi:vars>"#);
    let result = run(
        r#"<esi:include src="http://example.com/frag" dca="esi"/>"#,
        Configuration::default(),
        &d,
    )?;
    assert_eq!(result, "Y is 99");
    Ok(())
}

// ===========================================================================
// 2. max_include_depth tests
// ===========================================================================

/// Include at depth exactly at the limit is silently omitted.
#[test]
fn test_max_include_depth_omits_at_limit() -> esi::Result<()> {
    let d = static_body(r#"L0[<esi:include src="http://example.com/level1" dca="esi"/>]"#);
    let result = run(
        r#"Before<esi:include src="http://example.com/level0" dca="esi"/>After"#,
        Configuration::default().with_max_include_depth(1),
        &d,
    )?;
    // level0 processed (depth 0 < 1), level1 omitted (depth 1 >= 1)
    assert_eq!(result, "BeforeL0[]After");
    Ok(())
}

/// Include within depth limit is processed normally.
#[test]
fn test_max_include_depth_allows_within_limit() -> esi::Result<()> {
    let d = static_body("inner");
    let result = run(
        r#"<esi:include src="http://example.com/frag" dca="esi"/>"#,
        Configuration::default().with_max_include_depth(5),
        &d,
    )?;
    assert_eq!(result, "inner");
    Ok(())
}

/// Eval with dca="esi" at depth limit is omitted.
#[test]
fn test_max_include_depth_eval_dca_esi_omitted() -> esi::Result<()> {
    let d = static_body(r#"E0[<esi:eval src="http://example.com/e1" dca="esi"/>]"#);
    let result = run(
        r#"Before<esi:eval src="http://example.com/e0" dca="esi"/>After"#,
        Configuration::default().with_max_include_depth(1),
        &d,
    )?;
    assert_eq!(result, "BeforeE0[]After");
    Ok(())
}

/// Eval with dca="none" at depth limit is also omitted.
#[test]
fn test_max_include_depth_eval_dca_none_omitted() -> esi::Result<()> {
    let d = static_body(r#"E0[<esi:eval src="http://example.com/e1" dca="none"/>]"#);
    let result = run(
        r#"Before<esi:eval src="http://example.com/e0" dca="none"/>After"#,
        Configuration::default().with_max_include_depth(1),
        &d,
    )?;
    assert_eq!(result, "BeforeE0[]After");
    Ok(())
}

/// Default depth limit of 15.
#[test]
fn test_max_include_depth_default_is_15() {
    assert_eq!(Configuration::default().max_include_depth, 15);
}

// ===========================================================================
// 3. Edge-Control header tests
// ===========================================================================

/// Edge-Control: dca=esi causes fragment to be ESI-processed (when enabled).
#[test]
fn test_edge_control_dca_esi() -> esi::Result<()> {
    let d = with_edge_control(
        r#"<esi:assign name="v" value="42"/><esi:vars>$(v)</esi:vars>"#,
        "dca=esi",
    );
    let result = run(
        r#"<esi:include src="http://example.com/frag"/>"#,
        Configuration::default().with_edge_control(true),
        &d,
    )?;
    assert_eq!(result, "42");
    Ok(())
}

/// Edge-Control: dca=noop causes fragment to be inserted raw.
#[test]
fn test_edge_control_dca_noop() -> esi::Result<()> {
    let d = with_edge_control(r#"<esi:vars>raw</esi:vars>"#, "dca=noop");
    let result = run(
        r#"<esi:include src="http://example.com/frag"/>"#,
        Configuration::default()
            .with_edge_control(true)
            .with_default_dca(DcaMode::Esi),
        &d,
    )?;
    assert_eq!(result, "<esi:vars>raw</esi:vars>");
    Ok(())
}

/// Edge-Control header is ignored when enable_edge_control is false.
#[test]
fn test_edge_control_ignored_when_disabled() -> esi::Result<()> {
    let d = with_edge_control(
        r#"<esi:assign name="v" value="1"/><esi:vars>$(v)</esi:vars>"#,
        "dca=esi",
    );
    let result = run(
        r#"<esi:include src="http://example.com/frag"/>"#,
        Configuration::default(), // enable_edge_control=false, default_dca=None
        &d,
    )?;
    assert_eq!(
        result,
        r#"<esi:assign name="v" value="1"/><esi:vars>$(v)</esi:vars>"#
    );
    Ok(())
}

/// Explicit tag dca="none" beats Edge-Control: dca=esi.
#[test]
fn test_tag_dca_beats_edge_control() -> esi::Result<()> {
    let d = with_edge_control(r#"<esi:vars>should be raw</esi:vars>"#, "dca=esi");
    let result = run(
        r#"<esi:include src="http://example.com/frag" dca="none"/>"#,
        Configuration::default().with_edge_control(true),
        &d,
    )?;
    assert_eq!(result, "<esi:vars>should be raw</esi:vars>");
    Ok(())
}

/// Edge-Control with dca= alongside other directives.
#[test]
fn test_edge_control_mixed_directives() -> esi::Result<()> {
    let d = with_edge_control(
        r#"<esi:assign name="z" value="7"/><esi:vars>$(z)</esi:vars>"#,
        "no-store, dca=esi",
    );
    let result = run(
        r#"<esi:include src="http://example.com/frag"/>"#,
        Configuration::default().with_edge_control(true),
        &d,
    )?;
    assert_eq!(result, "7");
    Ok(())
}

/// Edge-Control with unrecognised dca value falls through to default.
#[test]
fn test_edge_control_unknown_dca_value() -> esi::Result<()> {
    let d = with_edge_control(r#"<esi:vars>raw</esi:vars>"#, "dca=xslt");
    let result = run(
        r#"<esi:include src="http://example.com/frag"/>"#,
        Configuration::default()
            .with_edge_control(true)
            .with_default_dca(DcaMode::None),
        &d,
    )?;
    assert_eq!(result, "<esi:vars>raw</esi:vars>");
    Ok(())
}

/// Edge-Control without dca= directive falls through to default.
#[test]
fn test_edge_control_no_dca_directive() -> esi::Result<()> {
    let d = with_edge_control(r#"<esi:vars>raw</esi:vars>"#, "no-store");
    let result = run(
        r#"<esi:include src="http://example.com/frag"/>"#,
        Configuration::default()
            .with_edge_control(true)
            .with_default_dca(DcaMode::None),
        &d,
    )?;
    assert_eq!(result, "<esi:vars>raw</esi:vars>");
    Ok(())
}

/// Edge-Control beats default_dca (header > config default).
#[test]
fn test_edge_control_beats_default_dca() -> esi::Result<()> {
    let d = with_edge_control(r#"<esi:vars>raw</esi:vars>"#, "dca=noop");
    let result = run(
        r#"<esi:include src="http://example.com/frag"/>"#,
        Configuration::default()
            .with_edge_control(true)
            .with_default_dca(DcaMode::Esi),
        &d,
    )?;
    assert_eq!(result, "<esi:vars>raw</esi:vars>");
    Ok(())
}

// ===========================================================================
// 4. inherit_parent_dca tests
// ===========================================================================

/// Inheritance off + default=None: child inside dca=esi parent is NOT ESI-processed.
#[test]
fn test_inherit_off_child_uses_default() -> esi::Result<()> {
    let call_count = Arc::new(AtomicUsize::new(0));
    let cc = call_count.clone();
    let d =
        move |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            let n = cc.fetch_add(1, Ordering::SeqCst);
            let body = if n == 0 {
                r#"OUTER[<esi:include src="http://example.com/child"/>]"#
            } else {
                r#"<esi:vars>INNER</esi:vars>"#
            };
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                Response::from_body(body),
            )))
        };
    let result = run(
        r#"<esi:include src="http://example.com/frag0" dca="esi"/>"#,
        Configuration::default(), // inherit=false, default=None
        &d,
    )?;
    assert_eq!(result, "OUTER[<esi:vars>INNER</esi:vars>]");
    Ok(())
}

/// Inheritance on + default=None: child inside dca=esi parent IS ESI-processed.
#[test]
fn test_inherit_on_child_inherits_esi() -> esi::Result<()> {
    let call_count = Arc::new(AtomicUsize::new(0));
    let cc = call_count.clone();
    let d =
        move |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            let n = cc.fetch_add(1, Ordering::SeqCst);
            let body = if n == 0 {
                r#"OUTER[<esi:include src="http://example.com/child"/>]"#
            } else {
                r#"<esi:assign name="v" value="42"/><esi:vars>$(v)</esi:vars>"#
            };
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                Response::from_body(body),
            )))
        };
    let result = run(
        r#"<esi:include src="http://example.com/frag0" dca="esi"/>"#,
        Configuration::default().with_inherit_parent_dca(true),
        &d,
    )?;
    assert_eq!(result, "OUTER[42]");
    Ok(())
}

/// Inheritance on: top-level include (depth=0) falls to default, not Esi.
#[test]
fn test_inherit_on_top_level_uses_default() -> esi::Result<()> {
    let d = static_body(r#"<esi:vars>raw</esi:vars>"#);
    let result = run(
        r#"<esi:include src="http://example.com/frag"/>"#,
        Configuration::default().with_inherit_parent_dca(true),
        &d,
    )?;
    assert_eq!(result, "<esi:vars>raw</esi:vars>");
    Ok(())
}

/// Inheritance on + explicit dca="none" on child → still None (tag wins).
#[test]
fn test_inherit_on_explicit_dca_none_wins() -> esi::Result<()> {
    let call_count = Arc::new(AtomicUsize::new(0));
    let cc = call_count.clone();
    let d =
        move |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            let n = cc.fetch_add(1, Ordering::SeqCst);
            let body = if n == 0 {
                r#"OUTER[<esi:include src="http://example.com/child" dca="none"/>]"#
            } else {
                r#"<esi:vars>INNER</esi:vars>"#
            };
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                Response::from_body(body),
            )))
        };
    let result = run(
        r#"<esi:include src="http://example.com/frag0" dca="esi"/>"#,
        Configuration::default().with_inherit_parent_dca(true),
        &d,
    )?;
    assert_eq!(result, "OUTER[<esi:vars>INNER</esi:vars>]");
    Ok(())
}

/// Inheritance on + Edge-Control dca=noop on child → still None (header beats inheritance).
#[test]
fn test_inherit_on_edge_control_beats_inheritance() -> esi::Result<()> {
    let call_count = Arc::new(AtomicUsize::new(0));
    let cc = call_count.clone();
    let d =
        move |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            let n = cc.fetch_add(1, Ordering::SeqCst);
            if n == 0 {
                Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                    Response::from_body(r#"OUTER[<esi:include src="http://example.com/child"/>]"#),
                )))
            } else {
                let mut resp = Response::from_body(r#"<esi:vars>INNER</esi:vars>"#);
                resp.set_header("Edge-Control", "dca=noop");
                Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                    resp,
                )))
            }
        };
    let result = run(
        r#"<esi:include src="http://example.com/frag0" dca="esi"/>"#,
        Configuration::default()
            .with_edge_control(true)
            .with_inherit_parent_dca(true),
        &d,
    )?;
    assert_eq!(result, "OUTER[<esi:vars>INNER</esi:vars>]");
    Ok(())
}

/// Inheritance on + mixed subtrees: only the dca=esi subtree inherits.
#[test]
fn test_inherit_on_mixed_subtrees() -> esi::Result<()> {
    let call_count = Arc::new(AtomicUsize::new(0));
    let cc = call_count.clone();
    let d =
        move |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            let n = cc.fetch_add(1, Ordering::SeqCst);
            let body = match n {
                0 => r#"A[<esi:include src="http://example.com/A1"/>]"#,
                1 => r#"<esi:assign name="v" value="1"/><esi:vars>$(v)</esi:vars>"#,
                2 => r#"<esi:vars>RAW</esi:vars>"#,
                _ => "unexpected",
            };
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                Response::from_body(body),
            )))
        };
    let result = run(
        r#"<esi:include src="http://example.com/A" dca="esi"/><esi:include src="http://example.com/C"/>"#,
        Configuration::default().with_inherit_parent_dca(true),
        &d,
    )?;
    // A's child inherits ESI, C is raw (top-level, default=None)
    assert_eq!(result, "A[1]<esi:vars>RAW</esi:vars>");
    Ok(())
}

/// Inheritance on with eval: child of dca=esi eval inherits ESI.
#[test]
fn test_inherit_on_eval_subtree() -> esi::Result<()> {
    let call_count = Arc::new(AtomicUsize::new(0));
    let cc = call_count.clone();
    let d =
        move |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            let n = cc.fetch_add(1, Ordering::SeqCst);
            let body = if n == 0 {
                r#"E0[<esi:include src="http://example.com/child"/>]"#
            } else {
                r#"<esi:assign name="w" value="88"/><esi:vars>$(w)</esi:vars>"#
            };
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                Response::from_body(body),
            )))
        };
    let result = run(
        r#"<esi:eval src="http://example.com/e0" dca="esi"/>"#,
        Configuration::default().with_inherit_parent_dca(true),
        &d,
    )?;
    assert_eq!(result, "E0[88]");
    Ok(())
}
