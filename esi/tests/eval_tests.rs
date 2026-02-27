use esi::{Configuration, Processor};
use fastly::{Request, Response};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

/// Test that esi:eval with dca="none" processes in parent's context (spec Example 1)
/// Variables from fragment ARE accessible in parent
#[test]
fn test_eval_dca_none_parent_context() -> esi::Result<()> {
    // Parent sets pvar1=7 and pvar2=8, then evals fragment with dca="none"
    let input = r#"
<esi:assign name="pvar1" value="7"/>
<esi:assign name="pvar2" value="8"/>
  <esi:eval src="http://example.com/frag1.html" dca="none"/>
<esi:vars>pvar1 = $(pvar1)
  pvar2 = $(pvar2)
  fvar = $(fvar)
</esi:vars>"#;

    let dispatcher =
        |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            // Fragment sets fvar=9 and pvar2=0
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                Response::from_body(
                    r#"
<esi:assign name="fvar" value="9"/>
<esi:assign name="pvar2" value="0"/>"#,
                ),
            )))
        };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(None, Configuration::default());
    processor.process_stream(reader, &mut output, Some(&dispatcher), None)?;

    let result = String::from_utf8(output).unwrap();
    // With dca="none", fragment executes in parent context
    // So parent's pvar1=7 stays, fragment's pvar2=0 overrides parent's pvar2=8, fragment's fvar=9 is set
    assert_eq!(
        result.trim(),
        r#"pvar1 = 7
  pvar2 = 0
  fvar = 9"#,
        "Fragment should execute in parent context, variables should be shared/overridden"
    );
    Ok(())
}

/// Test that esi:eval with dca="esi" processes in isolated context (spec Example 2)
/// Variables from fragment are NOT accessible in parent
#[test]
fn test_eval_dca_esi_isolated_context() -> esi::Result<()> {
    // Same setup as Example 1, but with dca="esi"
    let input = r#"
<esi:assign name="pvar1" value="7"/>
<esi:assign name="pvar2" value="8"/>
<esi:eval src="http://example.com/frag1.html" dca="esi"/>
<esi:vars>pvar1 = $(pvar1)
  pvar2 = $(pvar2)
  fvar = $(fvar)
</esi:vars>"#;

    let dispatcher =
        |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            // Fragment sets fvar=9 and pvar2=0 (same as Example 1)
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                Response::from_body(
                    r#"
<esi:assign name="fvar" value="9"/>
<esi:assign name="pvar2" value="0"/>"#,
                ),
            )))
        };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(None, Configuration::default());
    processor.process_stream(reader, &mut output, Some(&dispatcher), None)?;

    let result = String::from_utf8(output).unwrap();
    // With dca="esi", fragment executes in ISOLATED context first
    // Fragment's variables DON'T affect parent, only the output (which is empty) is inserted
    assert_eq!(
        result.trim(),
        r#"pvar1 = 7
  pvar2 = 8
  fvar ="#,
        "Parent variables should remain unchanged, fragment variables should not leak"
    );
    Ok(())
}

/// Test that esi:eval with dca="esi" inserts the output from isolated processing
#[test]
fn test_eval_dca_esi_with_output() -> esi::Result<()> {
    let input = r#"
<esi:assign name="parent_var" value="'from_parent'"/>
<esi:eval src="http://example.com/fragment" dca="esi"/>
<esi:vars>After: $(fragment_var)</esi:vars>"#;

    let dispatcher =
        |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            // Fragment sets a variable and outputs text
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                Response::from_body(
                    r#"
<esi:assign name="fragment_var" value="'from_fragment'"/>
<esi:vars>Output from fragment</esi:vars>"#,
                ),
            )))
        };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(None, Configuration::default());
    processor.process_stream(reader, &mut output, Some(&dispatcher), None)?;

    let result = String::from_utf8(output).unwrap();
    // With dca="esi", phase 1 processes fragment in isolation (output produced, vars stay isolated)
    // Phase 2 processes that output in parent context (fragment_var not accessible)
    assert_eq!(
        result.trim(),
        "Output from fragment\nAfter:",
        "Should output text from fragment, but fragment variables should not leak to parent"
    );
    Ok(())
}

/// Test that include with dca="none" inserts content verbatim (no ESI processing)
#[test]
fn test_include_dca_none_no_processing() -> esi::Result<()> {
    let input = r#"<esi:include src="http://example.com/fragment" dca="none"/>"#;

    let dispatcher =
        |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            // Return content with ESI tags - should NOT be processed
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                Response::from_body(
                    r#"<esi:assign name="x" value="42"/><esi:vars>X is $(x)</esi:vars>"#,
                ),
            )))
        };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(None, Configuration::default());
    processor.process_stream(reader, &mut output, Some(&dispatcher), None)?;

    let result = String::from_utf8(output).unwrap();
    assert_eq!(
        result, r#"<esi:assign name="x" value="42"/><esi:vars>X is $(x)</esi:vars>"#,
        "dca='none' should insert content verbatim without ESI processing"
    );
    Ok(())
}

/// Test that include with dca="esi" processes content as ESI
#[test]
fn test_include_dca_esi_processes_content() -> esi::Result<()> {
    let input = r#"<esi:include src="http://example.com/fragment" dca="esi"/>"#;

    let dispatcher =
        |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            // Return ESI content - should be processed
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                Response::from_body(
                    r#"<esi:assign name="y" value="99"/><esi:vars>Y is $(y)</esi:vars>"#,
                ),
            )))
        };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(None, Configuration::default());
    processor.process_stream(reader, &mut output, Some(&dispatcher), None)?;

    let result = String::from_utf8(output).unwrap();
    assert_eq!(result, "Y is 99", "dca='esi' should process content as ESI");
    Ok(())
}

/// Test that include with dca="esi" processes in parent namespace (like eval)
#[test]
fn test_include_dca_esi_parent_namespace() -> esi::Result<()> {
    let input = r#"<esi:include src="http://example.com/fragment" dca="esi"/><esi:vars>After include: $(shared_var)</esi:vars>"#;

    let dispatcher =
        |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            // Set a variable in the included ESI
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                Response::from_body(r#"<esi:assign name="shared_var" value="'shared'"/>"#),
            )))
        };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(None, Configuration::default());
    processor.process_stream(reader, &mut output, Some(&dispatcher), None)?;

    let result = String::from_utf8(output).unwrap();
    assert_eq!(
        result, "After include: shared",
        "Include with dca='esi' should process in parent namespace"
    );
    Ok(())
}

/// Test complex scenario: include respects dca, eval always processes as ESI
#[test]
fn test_eval_vs_include_dca_difference() -> esi::Result<()> {
    let input = r#"<esi:include src="http://example.com/raw"/><esi:eval src="http://example.com/processed"/>"#;

    // Track which URLs were called
    let calls = Arc::new(Mutex::new(HashMap::new()));
    let calls_clone = calls.clone();

    let dispatcher =
        move |req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            let url = req.get_url().to_string();
            calls_clone.lock().unwrap().insert(url.clone(), true);

            let content = match url.as_str() {
                "http://example.com/raw" => r#"<esi:vars>RAW</esi:vars>"#,
                "http://example.com/processed" => r#"<esi:vars>PROCESSED</esi:vars>"#,
                _ => "UNKNOWN",
            };

            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                Response::from_body(content),
            )))
        };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(None, Configuration::default());
    processor.process_stream(reader, &mut output, Some(&dispatcher), None)?;

    let result = String::from_utf8(output).unwrap();
    // Include without dca should insert verbatim (ESI not processed)
    // Eval without dca defaults to "none" which processes in parent context
    assert_eq!(
        result, r#"<esi:vars>RAW</esi:vars>PROCESSED"#,
        "Include without dca should insert verbatim, eval should process as ESI"
    );

    // Verify both URLs were called
    let call_map = calls.lock().unwrap();
    assert!(call_map.contains_key("http://example.com/raw"));
    assert!(call_map.contains_key("http://example.com/processed"));
    Ok(())
}

/// Test that eval with onerror="continue" inserts nothing on failure (per ESI spec)
#[test]
fn test_eval_onerror_continue() -> esi::Result<()> {
    let input = r#"Before<esi:eval src="http://example.com/fail" onerror="continue"/>After"#;

    let dispatcher =
        |_req: Request, _maxwait: Option<u32>| -> esi::Result<esi::PendingFragmentContent> {
            // Return a failed response
            Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
                Response::from_status(500),
            )))
        };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(None, Configuration::default());
    processor.process_stream(reader, &mut output, Some(&dispatcher), None)?;

    let result = String::from_utf8(output).unwrap();
    // Per ESI spec: onerror="continue" deletes the tag with no output (not even a comment)
    assert_eq!(
        result, "BeforeAfter",
        "onerror='continue' should insert nothing on failure"
    );
    Ok(())
}

/// Test nested ESI in eval
#[test]
fn test_eval_with_nested_esi() -> esi::Result<()> {
    let input = r#"<esi:eval src="http://example.com/nested"/>"#;

    let call_count = Arc::new(Mutex::new(0));
    let call_count_clone = call_count.clone();

    let dispatcher = move |req: Request,
                           _maxwait: Option<u32>|
          -> esi::Result<esi::PendingFragmentContent> {
        let url = req.get_url().to_string();
        *call_count_clone.lock().unwrap() += 1;

        let content = match url.as_str() {
            "http://example.com/nested" => {
                // Return ESI with a choose block
                r#"<esi:choose><esi:when test="1 == 1">Chosen</esi:when><esi:otherwise>Not</esi:otherwise></esi:choose>"#
            }
            _ => "UNKNOWN",
        };

        Ok(esi::PendingFragmentContent::CompletedRequest(Box::new(
            Response::from_body(content),
        )))
    };

    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(None, Configuration::default());
    processor.process_stream(reader, &mut output, Some(&dispatcher), None)?;

    let result = String::from_utf8(output).unwrap();
    assert_eq!(
        result, "Chosen",
        "eval should process nested ESI constructs"
    );
    assert_eq!(
        *call_count.lock().unwrap(),
        1,
        "Should only call dispatcher once"
    );
    Ok(())
}
