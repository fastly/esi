use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use esi::parse;

// Benchmark group that matches the test cases from the bench branch (old XML parser)
// This allows direct comparison between the old parser and nom parser
fn benchmark_various_esi_documents(c: &mut Criterion) {
    let mut group = c.benchmark_group("esi_documents");

    // These test cases match exactly what's in the bench branch for fair comparison
    let documents = vec![
        (
            "simple_include",
            r#"<esi:include src="http://example.com/header.html"/>"#,
        ),
        (
            "try_block",
            r#"
            <esi:try>
                <esi:attempt><esi:include src="http://example.com/content.html"/></esi:attempt>
                <esi:except><p>Fallback</p></esi:except>
            </esi:try>
        "#,
        ),
        (
            "try_block_with_content",
            r#"
            <esi:try>
                <esi:attempt>
                    <esi:include src="http://example.com/content.html"/>
                    <p>Some content</p>
                </esi:attempt>
                <esi:except>
                    <p>Fallback content</p>
                </esi:except>
            </esi:try>
        "#,
        ),
        (
            "nested_try",
            r#"
            <esi:try>
                <esi:attempt>
                    <esi:try>
                        <esi:attempt><esi:include src="http://example.com/inner.html"/></esi:attempt>
                        <esi:except><p>Inner fallback</p></esi:except>
                    </esi:try>
                </esi:attempt>
                <esi:except><p>Outer fallback</p></esi:except>
            </esi:try>
        "#,
        ),
        ("vars", r#"<esi:vars>$(HTTP_HOST)</esi:vars>"#),
        (
            "choose",
            r#"
            <esi:choose>
                <esi:when test="$(HTTP_COOKIE{type})=='premium'">
                    <p>Premium content</p>
                </esi:when>
                <esi:otherwise>
                    <p>Regular content</p>
                </esi:otherwise>
            </esi:choose>
        "#,
        ),
        (
            "complex_document",
            r#"
            <html>
                <esi:try>
                    <esi:attempt>
                        <esi:include src="http://example.com/header.html"/>
                    </esi:attempt>
                    <esi:except>
                        <p>Default header</p>
                    </esi:except>
                </esi:try>
                <esi:vars>$(HTTP_HOST)</esi:vars>
                <esi:choose>
                    <esi:when test="$(HTTP_COOKIE{type})=='premium'">
                        <p>Premium content</p>
                    </esi:when>
                    <esi:otherwise>
                        <p>Regular content</p>
                    </esi:otherwise>
                </esi:choose>
            </html>
        "#,
        ),
    ];

    for (name, xml) in documents {
        group.bench_with_input(BenchmarkId::from_parameter(name), &xml, |b, xml| {
            b.iter(|| {
                let result = parse(black_box(xml)).unwrap();
                black_box(result);
            });
        });
    }

    group.finish();
}

// Additional benchmark group for nom parser-specific features
// These test new capabilities not present in the old XML parser
fn benchmark_nom_parser_features(c: &mut Criterion) {
    let mut group = c.benchmark_group("nom_parser_features");

    let documents = vec![
        (
            "simple_text",
            r#"<html><body><p>Simple text content</p></body></html>"#,
        ),
        (
            "html_comment",
            r#"<!-- This is a comment --><p>Content</p>"#,
        ),
        (
            "vars_long",
            r#"<esi:vars>User agent: $(HTTP_USER_AGENT), Host: $(HTTP_HOST)</esi:vars>"#,
        ),
        ("assign_short", r#"<esi:assign name="test" value="hello"/>"#),
        (
            "assign_long",
            r#"<esi:assign name="test">Some value with $(VAR)</esi:assign>"#,
        ),
        (
            "choose_multiple_when",
            r#"
            <esi:choose>
                <esi:when test="$(HTTP_COOKIE{type})=='premium'">
                    <p>Premium content</p>
                </esi:when>
                <esi:when test="$(HTTP_COOKIE{type})=='basic'">
                    <p>Basic content</p>
                </esi:when>
                <esi:otherwise>
                    <p>Regular content</p>
                </esi:otherwise>
            </esi:choose>
        "#,
        ),
        (
            "expression_comparison",
            r#"<esi:choose>
                <esi:when test="$(count) > 10">High</esi:when>
                <esi:when test="$(count) <= 10 && $(count) >= 5">Medium</esi:when>
                <esi:otherwise>Low</esi:otherwise>
            </esi:choose>"#,
        ),
        (
            "expression_logical",
            r#"<esi:choose>
                <esi:when test="($(role) == 'admin') || ($(role) == 'moderator')">Access granted</esi:when>
                <esi:otherwise>Access denied</esi:otherwise>
            </esi:choose>"#,
        ),
        (
            "script_tag",
            r#"<html><head><script>console.log('test');</script></head><body>Content</body></html>"#,
        ),
        (
            "mixed_content",
            r#"
            <div>
                Text before
                <esi:include src="/fragment"/>
                Text after
                <esi:vars>$(VAR)</esi:vars>
                More text
                <!-- Comment -->
                <script>var x = 1;</script>
                Final text
            </div>
        "#,
        ),
    ];

    for (name, xml) in documents {
        group.bench_with_input(BenchmarkId::from_parameter(name), &xml, |b, xml| {
            b.iter(|| {
                let result = parse(black_box(xml)).unwrap();
                black_box(result);
            });
        });
    }

    group.finish();
}

fn benchmark_parser_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("parser_scaling");

    // Test how parser scales with document size
    let sizes = vec![100, 500, 1000, 5000, 10000];

    for size in sizes {
        let mut doc = String::new();
        doc.push_str("<html><body>");

        for i in 0..size {
            doc.push_str(&format!(
                r#"<div>Item {}</div><esi:vars>$(VAR_{})</esi:vars>"#,
                i, i
            ));
        }

        doc.push_str("</body></html>");

        group.bench_with_input(
            BenchmarkId::from_parameter(format!("elements_{}", size * 2)),
            &doc,
            |b, doc| {
                b.iter(|| {
                    let result = parse(black_box(doc)).unwrap();
                    black_box(result);
                });
            },
        );
    }

    group.finish();
}

fn benchmark_expression_parsing(c: &mut Criterion) {
    let mut group = c.benchmark_group("expression_parsing");

    let expressions = vec![
        ("simple_var", "$(VAR)"),
        ("var_with_key", "$(HTTP_COOKIE{name})"),
        ("var_with_default", "$(VAR|'default')"),
        ("integer", "42"),
        ("string", "'hello world'"),
        ("comparison_eq", "$(count) == 10"),
        ("comparison_ne", "$(status) != 'error'"),
        ("comparison_gt", "$(value) > 100"),
        ("comparison_lte", "$(score) <= 50"),
        ("logical_and", "$(a) == 1 && $(b) == 2"),
        ("logical_or", "$(x) == 'yes' || $(y) == 'no'"),
        ("negation", "!($(flag))"),
        ("grouped", "($(a) == 1) && ($(b) == 2)"),
        (
            "complex",
            "(($(role) == 'admin') || ($(role) == 'mod')) && $(active) != false",
        ),
        ("function_call", "$url_encode($(path))"),
        ("nested_function", "$base64_encode($url_encode($(text)))"),
    ];

    for (name, expr) in expressions {
        group.bench_with_input(BenchmarkId::from_parameter(name), &expr, |b, expr| {
            b.iter(|| {
                let result = esi::parse_expression(black_box(expr)).unwrap();
                black_box(result);
            });
        });
    }

    group.finish();
}

fn benchmark_interpolated_strings(c: &mut Criterion) {
    let mut group = c.benchmark_group("interpolated_strings");

    let strings = vec![
        ("no_interpolation", "Just plain text"),
        ("single_var", "Hello $(name)"),
        ("multiple_vars", "$(first) $(middle) $(last)"),
        (
            "mixed_content",
            "User: $(user), Email: $(email), Role: $(role)",
        ),
        (
            "with_html",
            "<div>Welcome $(user)!</div><p>Your score: $(score)</p>",
        ),
    ];

    for (name, string) in strings {
        group.bench_with_input(BenchmarkId::from_parameter(name), &string, |b, string| {
            b.iter(|| {
                let result = esi::parse_interpolated_string(black_box(string)).unwrap();
                black_box(result);
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    benchmark_various_esi_documents,
    benchmark_nom_parser_features,
    benchmark_parser_scaling,
    benchmark_expression_parsing,
    benchmark_interpolated_strings
);
criterion_main!(benches);
