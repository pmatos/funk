# fir test corpus

Texts that both fir parsers read, `funk-ir` in Rust (#9) and the Lean spec's
parser through `fir-ref` (#10), and the tests that the differential harness
runs on them (#13). The format is decided in
[ADR-2026-10-30-2050](../../docs/adrs/2026-10-30-2050-fir-test-corpus-format.md),
the harness in
[ADR-2026-10-30-2049](../../docs/adrs/2026-10-30-2049-differential-harness-in-python.md),
and how it judges a test in
[ADR-2026-10-30-2135](../../docs/adrs/2026-10-30-2135-harness-judges-tests-by-refinement.md)
and, for a run that makes choices,
[ADR-2026-10-31-0003](../../docs/adrs/2026-10-31-0003-harness-judges-differential-tests-by-outcome-sets.md).

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
  { func = "@freeze_sub", args = ["9223372036854775807"], results = [
    { values = ["0"], witness = ["5"] },
  ] },
  { func = "@freeze_poison", args = ["63"], choices = ["-64"], expect = ["-64"] },
]
```

- `func` is the function's symbol as text writes it. Write a quoted symbol
  in a TOML literal string, between single quotes.
- `args` gives one argument per parameter, each spelled as a constant of
  its type: `true` or `false` at `i1`, signed decimal at every other width.
  There are no `poison` arguments.
- `fuel` is `fir-ref run`'s budget, one step per op; 1,000,000 by default.
- Without `expect`, the test is differential. It runs on `fir-ref`, in
  exhaustive mode, and as native code from `funk build`, and the native
  result must refine one of `fir-ref`'s outcomes: the same number of
  values, each equal, or anything of its type where `fir-ref` returns
  poison. A run that makes no choice has one outcome. UB or fuel exhausted
  among the outcomes makes the test invalid, which counts as a failure:
  raise the fuel budget, or make the test interpreter-only.
- `results` declares a differential test's results, each a list of
  `values` and a `witness`: the choices on which `fir-ref run --choices`
  gives them. A test whose run chooses more than 16 bits on one path must
  declare its results; the harness checks each witness, and 32 seeded runs
  of `fir-ref run --seed` must each give a declared result. Within the
  budget, the declared results must be exactly the run's outcomes. A
  witness that no longer fits the run fails the test. Native code must
  refine one declared result.
- With `expect`, the test is interpreter-only: only `fir-ref` runs it, and
  it must give that result. `expect` is a list of values, each a value or
  `"poison"`, or `"ub"` (any reason), or `"fuel-exhausted"`. `choices`
  gives the path's choices, each spelled as a constant of its type; there
  are none by default, so a run that chooses needs them.

`funk build` builds a module all or nothing. So a module with a
differential test holds only functions that the backend lowers: today
`const`, `add`, `sub` and `mul` with any flags, `freeze`, the bitwise ops
and shifts, `zext`, `sext`, `trunc`, `sdiv` and `udiv` with or without
`exact`, `srem`, `urem`, `icmp`, `select` and `ret` at `i1`, `i8`, `i16`,
`i32` and `i64`, with at most one result. Tests of other widths, or of
several results, go in modules whose tests are all interpreter-only, such
as `tracer-i7.fir` and `widths.fir`.

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

The texts use `const`, `add`, `sub` and `mul` with their flags `nuw` and
`nsw`, `freeze` and `ret`, but for must-reject texts that name an op or a
flag that fir does not have. `add-iN`, `sub-iN` and `mul-iN` run each op
with each set of flags on every pair of boundary bit patterns,
`poison-iN` how poison propagates through them, and `freeze-iN` `freeze`
of values and of poison, at `i1`, `i7`, `i8`, `i16`, `i32`, `i33` and
`i64`; `reject/arith.toml` holds the texts of these ops that do not
decode (#14).

The texts of #15 also use `and`, `or`, `xor`, `shl`, `lshr` and `ashr`.
`bitwise-iN` runs `and`, `or` and `xor` on every pair of boundary bit
patterns; `shift-iN` shifts each boundary bit pattern with `shl`, `lshr`
and `ashr` by 0, 1, `N - 1`, `N`, `N + 1` and the boundary bit patterns;
and `poison-bitwise-iN` passes poison to each of the six ops as either
operand; all at the same seven widths. `freeze-xor-i64` runs `xor %f, %f`
on a frozen poison. `reject/bitwise.toml` and `reject/shift.toml` hold
the texts of these ops that do not decode.

The texts also use `zext`, `sext` and `trunc` (#17). `zext.fir`,
`sext.fir` and `trunc.fir` run each width change at every valid pair of
`i1`, `i8`, `i16`, `i32` and `i64`, on the boundary bit patterns of its
operand; `zext-i7`, `zext-i33` and their `sext` and `trunc` twins run
them to and from `i7` and `i33`, and `zext-poison`, `sext-poison` and
`trunc-poison` on a poison operand. `reject/width.toml` holds their texts
that do not decode or do not validate.

The texts of #18 use `sdiv` and `udiv`, each with and without `exact`,
`srem` and `urem`. `div-iN` runs them on every pair of boundary bit
patterns at the seven widths above; a pair that is UB in the spec, and
every pair at `i7` and `i33`, is an interpreter-only test, and at the
other widths each defined pair of `exact` also has an interpreter-only
twin. `div-i8-ax` tests the `i8` lowering, which divides through `%ax`,
on its own. `poison-div-iN` passes poison to each of them as either
operand and as both, at the seven widths. #18's differential test with
a frozen divisor that can be zero is invalid, so it is not in this
corpus: it is in the fixture corpus `scripts/harness/fixtures/invalid/`,
and `scripts/check-harness.sh` checks that the harness reports it
invalid because `the set holds UB (sdiv by zero)` (ADR-2026-10-31-0208).
`reject/div.toml` holds the texts of these ops that do not decode.

The texts of #16 also use `icmp` and `select`. `icmp-iN` runs `icmp`
with each of its ten predicates, and `select-iN` runs `select` with each
condition, on every pair of boundary bit patterns; `poison-compare-iN`
gives `icmp` a poison operand on either side, and `select` a poison
condition and a poison value, chosen and not chosen; all at the same
seven widths. `select-and` shows that `select %c, %x, false` may not
become `and %c, %x` where `%x` may be poison, and that
`and %c, %g` with `%g = freeze %x` may. `reject/compare.toml` holds the
texts of these ops that do not decode.

#19 and #20 add the other ops to `funk`.
