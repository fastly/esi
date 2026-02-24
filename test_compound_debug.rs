use esi::{Configuration, Processor};
use fastly::Request;

fn main() {
    // Test case: Cookie exists but doesn't match pattern
    let input = r#"
        <esi:choose>
            <esi:when test="!$exists($(HTTP_COOKIE{'UserInfo'})) || !($(HTTP_COOKIE{'UserInfo'}) matches '''UserId=[0-9]''')">
                when branch
            </esi:when>
            <esi:otherwise>
                otherwise branch
            </esi:otherwise>
        </esi:choose>
    "#;
    
    let mut req = Request::get("http://example.com/test");
    req.set_header("Cookie", "UserInfo=NoMatch");
    
    let reader = std::io::BufReader::new(std::io::Cursor::new(input.as_bytes()));
    let mut output = Vec::new();
    let mut processor = Processor::new(Some(req), Configuration::default());
    
    processor
        .process_stream(reader, &mut output, None, None)
        .expect("Processing should succeed");
    
    let result = String::from_utf8(output).unwrap();
    println!("Result:\n{}", result);
    
    if result.contains("when branch") {
        println!("\n✓ TEST PASSED: when branch executed as expected");
    } else if result.contains("otherwise branch") {
        println!("\n✗ TEST FAILED: otherwise branch executed, but should have been when branch");
        
        // Debug the expressions
        let mut req2 = Request::get("http://example.com/test");
        req2.set_header("Cookie", "UserInfo=NoMatch");
        
        let test1 = r#"<esi:vars>Cookie value: $(HTTP_COOKIE{'UserInfo'})</esi:vars>"#;
        let reader1 = std::io::BufReader::new(std::io::Cursor::new(test1.as_bytes()));
        let mut output1 = Vec::new();
        let mut processor1 = Processor::new(Some(req2), Configuration::default());
        processor1.process_stream(reader1, &mut output1, None, None).unwrap();
        println!("\nCookie value: {}", String::from_utf8(output1).unwrap());
        
        let mut req3 = Request::get("http://example.com/test");
        req3.set_header("Cookie", "UserInfo=NoMatch");
        let test2 = r#"<esi:vars>$exists result: $exists($(HTTP_COOKIE{'UserInfo'}))</esi:vars>"#;
        let reader2 = std::io::BufReader::new(std::io::Cursor::new(test2.as_bytes()));
        let mut output2 = Vec::new();
        let mut processor2 = Processor::new(Some(req3), Configuration::default());
        processor2.process_stream(reader2, &mut output2, None, None).unwrap();
        println!("Exists result: {}", String::from_utf8(output2).unwrap());
        
        let mut req4 = Request::get("http://example.com/test");
        req4.set_header("Cookie", "UserInfo=NoMatch");
        let test3 = r#"<esi:vars>Matches result: $(HTTP_COOKIE{'UserInfo'}) matches '''UserId=[0-9]'''</esi:vars>"#;
        let reader3 = std::io::BufReader::new(std::io::Cursor::new(test3.as_bytes()));
        let mut output3 = Vec::new();
        let mut processor3 = Processor::new(Some(req4), Configuration::default());
        processor3.process_stream(reader3, &mut output3, None, None).unwrap();
        println!("Matches result: {}", String::from_utf8(output3).unwrap());
    }
}
