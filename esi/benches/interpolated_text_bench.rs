use bytes::Bytes;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use esi::parse_remainder;

fn bench_interpolated_text(c: &mut Criterion) {
    // Test case 1: Plain text without any special characters
    let plain_text =
        Bytes::from("This is plain text without any dollar signs or angle brackets. ".repeat(100));

    // Test case 2: Text with dollar signs but not ESI patterns (common case - prices, etc)
    let text_with_dollars = Bytes::from("Price: $19.99, Sale: $5 off, Total: $14.99. ".repeat(100));

    // Test case 3: Text with ESI patterns that WILL trigger delimiter matching
    let text_with_esi =
        Bytes::from("<esi:vars>Before $(VAR) middle $func() after.</esi:vars>".repeat(100));

    // Test case 4: Mixed content
    let mixed =
        Bytes::from("Text $5.99 more <esi:vars>$(VAR)</esi:vars> text $100 end. ".repeat(100));

    c.bench_function("interpolated_text_plain", |b| {
        b.iter(|| {
            let _ = parse_remainder(black_box(&plain_text));
        })
    });

    c.bench_function("interpolated_text_with_dollars", |b| {
        b.iter(|| {
            let _ = parse_remainder(black_box(&text_with_dollars));
        })
    });

    c.bench_function("interpolated_text_with_esi", |b| {
        b.iter(|| {
            let _ = parse_remainder(black_box(&text_with_esi));
        })
    });

    c.bench_function("interpolated_text_mixed", |b| {
        b.iter(|| {
            let _ = parse_remainder(black_box(&mixed));
        })
    });
}

criterion_group!(benches, bench_interpolated_text);
criterion_main!(benches);
