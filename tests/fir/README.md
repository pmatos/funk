# fir test corpus

Texts that both fir parsers read, `funk-ir` in Rust (#9) and the Lean spec's
parser through `fir-ref` (#10), and the tests that the differential harness
runs on them (#13). The format is decided in
[ADR-2026-10-30-2050](../../docs/adrs/2026-10-30-2050-fir-test-corpus-format.md),
the harness in
[testing-and-harness.md](../../docs/decisions/testing-and-harness.md#the-harness-program),
and how it judges a test, a run that makes choices included, in
[ADR-2026-10-30-2135](../../docs/adrs/2026-10-30-2135-harness-judges-tests-by-refinement.md).
The [coverage matrix](../../docs/coverage/README.md) counts the tests
that exercise each op instance at each width, on each side
([ADR-2026-11-03-0557](../../docs/adrs/2026-11-03-0557-a-generated-matrix-counts-the-tests-of-each-cell.md)).

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
- `llvm/NAME.fir` is a canonical text ported by hand from an LLVM test,
  and `llvm/NAME.toml` lists its tests, as below; beside them are LLVM's
  licence, `llvm/LICENSE.TXT`, and a notice, `llvm/README.md`. Their
  files are under LLVM's licence, not funk's
  ([ADR-2026-11-03-0643](../../docs/adrs/2026-11-03-0643-ported-llvm-tests-keep-llvm-s-licence-and-name-their-source.md)).

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
  its type: `true` or `false` at `i1`, signed decimal at every other width,
  and a float as its constants are spelled, as `1.0` or `0x7fc00000`
  (ADR-2026-11-11-1438); or
  `poison`, at any integer or float type (#123).
- `fuel` is `fir-ref run`'s budget, one step per op; 1,000,000 by default.
- Without `expect`, the test is differential. It runs on `fir-ref`, in
  exhaustive mode, and as native code from `funk build`, and the native result
  must refine one of `fir-ref`'s outcomes: the same number of values, each
  equal, or anything of its type where `fir-ref` returns poison. A run that
  makes no choice has one outcome. UB or fuel exhausted among the outcomes
  makes the test invalid, which counts as a failure: raise the fuel budget, or
  make the test interpreter-only. A native run that outgrows its stack makes
  the test invalid too: recurse less deep, or raise `ulimit -s`
  ([testing-and-harness.md](../../docs/decisions/testing-and-harness.md#a-run-that-outgrows-its-stack)).
  Native code takes no `poison`: it runs on each
  combination of stand-ins in its place, the boundary bit patterns of its type,
  and each result must refine one of `fir-ref`'s outcomes on the poison
  ([testing-and-harness.md](../../docs/decisions/testing-and-harness.md#poison-arguments)).
- `results` declares a differential test's results, each a list of
  `values` and a `witness`: the choices on which `fir-ref run --choices`
  gives them. A test whose run chooses more than 16 bits on one path must
  declare its results; the harness checks each witness, and 32 seeded runs
  of `fir-ref run --seed` must each give a declared result. Within the
  budget, the declared results must be exactly the run's outcomes. A
  witness that no longer fits the run fails the test. Native code must
  refine one declared result. When it fails on a poison stand-in, the
  harness runs `fir-ref` on that vector too: UB or fuel exhausted there
  makes the test invalid.
- With `expect`, the test is interpreter-only: only `fir-ref` runs it, and
  it must give that result. `expect` is a list of values, each a value or
  `"poison"`, or `"ub"` (any reason), or `"fuel-exhausted"`. `choices`
  gives the path's choices, each spelled as a constant of its type; there
  are none by default, so a run that chooses needs them.

`funk build` builds a module all or nothing. So a module with a
differential test holds only functions that the backend lowers: today
`const`, `poison`, `add`, `sub` and `mul` with any flags, `freeze`, the
bitwise ops and shifts, `zext`, `sext`, `trunc`, `sdiv` and `udiv` with
or without `exact`, `srem`, `urem`, `icmp`, `select`, `br`, `cond_br`,
`ret`, `unreachable` and `call` at `i1`, `i8`, `i16`, `i32`, `i64` and
`i128`, with any number of results. A test whose run reaches
`unreachable` is interpreter-only, since a native run of UB proves
nothing. Tests of other widths go in modules whose tests are all
interpreter-only, such as `tracer-i7.fir` and `widths.fir`.

## Must-reject texts

Each `[[reject]]` table of a `reject/*.toml` file is one text that breaks
one rule. When the ops that `funk` has cannot break a rule alone, such as
the scope of a value defined in a region, the text breaks a second rule
too, and `rule` names both.

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
- `scripts/harness/fuzz_to_corpus.py` adds an input that crashed a fuzzer,
  once the bug is fixed
  ([testing-and-harness-generated.md](../../docs/decisions/testing-and-harness-generated.md#fuzzing)).
- `scripts/harness/coverage.py`, the `coverage-matrix` hook, writes the
  coverage matrix from the tests and fails when the committed one is
  stale or a cell has no test. Run it with `--write` after changing a
  test.
- `crates/funk-ir/tests/corpus.rs` checks the canonical and non-canonical
  texts in Rust, those of `llvm/` among the canonical ones.
- `scripts/check-fir-ref.sh test` checks them, `llvm/` too, with `fir-ref fmt`,
  and that `fir-ref validate` accepts each one. It also runs functions of
  `add.fir`, `locations.fir`, `names.fir`, `results.fir`, `seven.fir`,
  `symbols.fir` and `widths.fir`, and of `noncanonical/add.fir`, with
  `fir-ref run`, and checks each result against a table in
  `scripts/check-fir-ref-run.sh`, which it calls
  ([fir-ref-command-line.md](../../docs/decisions/fir-ref-command-line.md#fir-ref-run)).
  Editing one of those files means updating that table.
  `scripts/check-fir-ref.sh round-trip` has Lean reprint what Rust prints from
  them, byte for byte
  ([testing-and-harness.md](../../docs/decisions/testing-and-harness.md#lean-tests-and-the-checks-of-fir-ref)).

## The texts

[`docs/coverage/texts.md`](../../docs/coverage/texts.md) says what each
family of texts tests, in the order their tickets added them. A ticket
that adds texts says what they test there.

## Cases ported from LLVM

The modules of `llvm/` are LLVM test cases ported to fir by hand (#23).
[`llvm/README.md`](llvm/README.md) lists them, says where each comes
from and how the cases were rewritten, and shows the two keys that a
ported sidecar has more than the format above, both required: `source`,
the LLVM test file and the llvm-project commit it was read at, and each
test's `from`, the LLVM function, or its CHECK or RUN lines, that the
test's function is.
