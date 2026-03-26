# ESI Parser Benchmarks

This directory contains benchmarks for the nom-based ESI parser.

## Running Benchmarks

To run all benchmarks:

```bash
cargo bench --bench parser_benchmarks
```

To run a specific benchmark group:

```bash
cargo bench --bench parser_benchmarks -- esi_parser
cargo bench --bench parser_benchmarks -- parser_scaling
cargo bench --bench parser_benchmarks -- expression_parsing
cargo bench --bench parser_benchmarks -- interpolated_strings
```

To run a specific benchmark:

```bash
cargo bench --bench parser_benchmarks -- "simple_include"
```

## Benchmark Groups

### 1. `esi_documents` ⚖️

**Direct comparison with bench branch (old XML parser)**

This group uses the exact same test cases as the `bench` branch to enable
apples-to-apples performance comparison between the old XML parser and the new nom parser.

Test cases:

- simple_include
- try_block
- try_block_with_content
- nested_try
- vars
- choose
- complex_document

### 2. `nom_parser_features`

Tests nom parser-specific features and improvements:

- HTML comments parsing
- Script tag handling
- Variable assignments (assign)
- Advanced expressions (comparison operators, logical operators)
- Mixed content with multiple ESI directives

### 3. `parser_scaling`

Tests how the parser scales with document size:

- 100, 500, 1000, 5000, and 10000 element documents
- Measures parsing performance as document complexity grows

### 4. `expression_parsing`

Tests ESI expression parsing performance:

- Simple variables
- Variables with keys (e.g., `$(HTTP_COOKIE{name})`)
- Variables with defaults
- Comparison operators (==, !=, >, <, >=, <=)
- Logical operators (&, |)
- Negation (!)
- Grouped expressions with parentheses
- Complex nested expressions

### 5. `interpolated_strings`

Tests parsing of strings with interpolated variables:

- Plain text (no interpolation)
- Single variable
- Multiple variables
- Mixed content with HTML

## Interpreting Results

Criterion will output:

- **Time per iteration**: How long each benchmark takes to run
- **Throughput**: How many operations per second (where applicable)
- **Change detection**: Comparison with previous runs to detect regressions

Results are saved in `target/criterion/` and include HTML reports.

## Viewing Reports

After running benchmarks, open the HTML reports:

```bash
open target/criterion/report/index.html
```

## Comparing with the Old XML Parser (bench branch)

To compare the nom parser performance with the old XML parser:

1. Run benchmarks on the bench branch (old XML parser):

   ```bash
   git checkout bench
   cargo bench --bench esi_processing
   ```

2. Switch to nom-parser-integration and run the comparison benchmark:
   ```bash
   git checkout nom-parser-integration
   cargo bench --bench parser_benchmarks -- esi_documents
   ```

The `esi_documents` benchmark group uses the **exact same test cases** as the bench branch,
ensuring a fair apples-to-apples comparison between the two parsers.

## Comparing Between Branches

To compare performance between any two branches:

1. Run benchmarks on the baseline branch:

   ```bash
   git checkout main
   cargo bench --bench parser_benchmarks
   ```

2. Switch to your branch and run again:
   ```bash
   git checkout your-branch
   cargo bench --bench parser_benchmarks
   ```

Criterion will automatically show the performance difference.

## Notes

- Benchmarks run with optimizations enabled (`--release`)
- Each benchmark is run multiple times to get accurate measurements
- Warm-up iterations are performed before measurement
- Results may vary based on system load and hardware
