# fir test corpus

Texts that both fir parsers read, `funk-ir` in Rust (#9) and the Lean spec's
parser through `fir-ref` (#10), and the tests that the differential harness
runs on them (#13). The format is decided in
[ADR-2026-10-30-2050](../../docs/adrs/2026-10-30-2050-fir-test-corpus-format.md),
the harness in
[ADR-2026-10-30-2049](../../docs/adrs/2026-10-30-2049-differential-harness-in-python.md),
and how it judges a test in
[ADR-2026-10-30-2135](../../docs/adrs/2026-10-30-2135-harness-judges-tests-by-refinement.md).

## Layout

- `canonical/NAME.fir` is a canonical text: exactly what the printer
  writes, with no comments, so `print(parse(t)) == t`. It is a valid
  module. Every `.fir` file outside the must-reject and non-canonical sets
  is canonical.
- `canonical/NAME.toml`, if present, lists the tests of `NAME.fir`.
  Metadata always lives outside the `.fir` text.
- `noncanonical/NAME.fir` is an input with comments, extra whitespace or
  other layout. It parses to the same module as `canonical/NAME.fir`, which
  is its canonical form.
- `reject/*.toml` holds the must-reject texts, grouped by what they break.

The corpus holds nothing else: the harness fails on any other file, and on
a key that the format below does not have.

## Tests

A sidecar lists tests, one TOML inline table each:

```toml
tests = [
  { func = "@add3", args = ["1", "2", "3"] },
  { func = '@"a b"' },
  { func = "@odd", args = ["1", "1"], expect = ["-63", "-4294967296"] },
  { func = "@seven", fuel = 1, expect = "fuel-exhausted" },
]
```

- `func` is the function's symbol as text writes it. Write a quoted symbol
  in a TOML literal string, between single quotes.
- `args` gives one argument per parameter, each spelled as a constant of
  its type: `true` or `false` at `i1`, signed decimal at every other width.
  There are no `poison` arguments.
- `fuel` is `fir-ref run`'s budget, one step per op; 1,000,000 by default.
- Without `expect`, the test is differential. It runs on `fir-ref` and as
  native code from `funk build`, and the native result must refine
  `fir-ref`'s: the same number of values, each equal, or anything of its
  type where `fir-ref` returns poison. A `fir-ref` result of UB or fuel
  exhausted makes the test invalid, which counts as a failure: raise the
  fuel budget, or make the test interpreter-only.
- With `expect`, the test is interpreter-only: only `fir-ref` runs it, and
  it must give that result. `expect` is a list of values, each a value or
  `"poison"`, or `"ub"` (any reason), or `"fuel-exhausted"`.

`funk build` builds a module all or nothing. So a module with a
differential test holds only functions that the backend lowers: today
`const`, `add`, `sub` and `mul` with any flags, `freeze`, `zext`, `sext`,
`trunc` and `ret` at `i1`, `i8`, `i16`, `i32` and `i64`, with at most one
result. Tests of other widths, or of several results, go in modules whose
tests are all interpreter-only, such as `tracer-i7.fir` and `widths.fir`.

## Must-reject texts

Each `[[reject]]` table of a `reject/*.toml` file is one text that breaks
one rule. When the ops that `funk` has cannot break a rule alone, such as
a rule of successors, the text breaks a second rule too, and `rule` names
both.

```toml
[[reject]]
verdict = "validation-error"
rule = "ret returns the function's result types: an i32 where it returns an i64"
text = '''
func @f(%a: i32) -> i64 {
^e:
  ret %a @0
}

locs {
  @0 = unknown
}
'''
```

- `verdict` is `parse-error` (the text does not decode) or
  `validation-error` (it parses, and validation rejects it). Both
  `funk verify` and `fir-ref validate` must give it, and a parse error at
  the same line and column.
- `rule` says, in words, which rule the text breaks.
- `text` is the text. A multi-line literal string (`'''`) holds it as it
  is. Characters that the repository's hooks keep out of files, such as a
  carriage return, a bidirectional control or a NUL, and a text with no
  final line feed, are written in a basic string with escapes: `\r`,
  `\u202e`, `\u0000`. A text that is not UTF-8 is a list of strings and
  bytes: `text = ["name(\"a", 0xff, "b\")"]` holds the byte `ff` between
  two strings written in UTF-8.

## Who reads it

- `scripts/check-harness.sh`, the differential harness and the
  `fir-harness` hook, runs everything above, and checks that both tools
  accept every module of the Rust generator.
- `crates/funk-ir/tests/corpus.rs` checks the canonical and non-canonical
  texts in Rust.
- `scripts/check-fir-ref.sh test` checks them with `fir-ref fmt`, and that
  `fir-ref validate` accepts each one. It also runs functions of
  `add.fir`, `locations.fir`, `names.fir`, `results.fir`, `seven.fir`,
  `symbols.fir` and `widths.fir`, and of `noncanonical/add.fir`, with
  `fir-ref run`, and checks each result against a table of its own
  (ADR-2026-10-30-1856). Editing one of those files means updating that
  table. `scripts/check-fir-ref.sh round-trip` has Lean reprint what Rust
  prints from them, byte for byte (ADR-2026-10-30-1250).

Today the texts use only `const`, `add` without flags and `ret`, but for
must-reject texts that name an op or a flag that fir does not have. Both
tools now also have `sub`, `mul`, their flags `nuw` and `nsw`, and `freeze`
(#14), and stage 3 of #14 adds texts for them. #15 to #20 add the other ops
to `funk`.
