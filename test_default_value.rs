use bytes::Bytes;
use esi::{Configuration, Processor};

fn main() {
    // Test 1: Default with string literal
    let input1 = Bytes::from_static(b"Value: $(UNDEFINED|'default_value')");
    let mut processor = Processor::new(None, Configuration::default());
    let result1 = processor.process_esi(&input1, false).unwrap();
    let output1 = String::from_utf8(result1.to_vec()).unwrap();
    println!("Test 1 - String default: {}", output1);

    // Test 2: Default with integer
    let input2 = Bytes::from_static(b"Value: $(UNDEFINED|42)");
    let mut processor = Processor::new(None, Configuration::default());
    let result2 = processor.process_esi(&input2, false).unwrap();
    let output2 = String::from_utf8(result2.to_vec()).unwrap();
    println!("Test 2 - Integer default: {}", output2);

    // Test 3: Variable with subscript and default
    let input3 = Bytes::from_static(b"Cookie: $(HTTP_COOKIE{'cobrand'}|'akamai')");
    let mut processor = Processor::new(None, Configuration::default());
    let result3 = processor.process_esi(&input3, false).unwrap();
    let output3 = String::from_utf8(result3.to_vec()).unwrap();
    println!("Test 3 - Cookie with default: {}", output3);
}
