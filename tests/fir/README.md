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
`exact`, `srem`, `urem`, `icmp`, `select`, `br`, `cond_br`, `ret` and
`call` at `i1`, `i8`, `i16`, `i32`, `i64` and `i128`, with any number
of results. Tests of other widths go in modules whose tests are all
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
- `scripts/harness/coverage.py`, the `coverage-matrix` hook, writes the
  coverage matrix from the tests and fails when the committed one is
  stale or a cell has no test. Run it with `--write` after changing a
  test.
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

The texts of #19 also use `br` and `cond_br`, which pass values to block
arguments. `branch-iN` passes each boundary bit pattern through `br`, and
every pair of them through `cond_br` with each condition; `loop-iN` runs
loops: the loop of the spec's `@sum`, an iterative factorial and Euclid's
gcd; `permute-iN` passes block arguments that swap and rotate each other
round a loop; and `poison-branch-iN` passes poison to block arguments,
where it arrives as poison, and branches on poison, which is UB; all at
the same seven widths. `sum` runs the spec's `@sum` itself, and `fuel`
runs loops that never end, which run out of fuel at the budget that each
test sets. `select-cond-br` shows that `select %c, %x, %y` may not become
a `cond_br` on `%c` where `%c` may be poison, and that a `cond_br` on
`freeze %c` may. `reject/branch.toml` holds the texts of these ops that
do not decode, and `reject/validation-branch.toml` those that break a
rule of validation that they bring into play: of successors and their
block arguments, terminators, dominance and reachability.

The texts of #20 also use `call`. `call-iN` passes each boundary bit
pattern through a call, as an argument and as its result, and every
pair of them to a callee that subtracts; `recursion-iN` runs a recursive
factorial and Fibonacci, and even and odd, which call each other; and
`poison-call-iN` passes poison to a callee and returns it from one, and
calls a callee that hits UB, which is UB of its caller; all at the same
seven widths. A run that never ends is interpreter-only, since a
differential test that runs out of fuel is invalid. A differential test
recurses at most 20 deep, and a deeper run is interpreter-only too.
PR #93 set that cap while a built executable's stack was its function's
frame, its wrapper's and 16 KiB, and the harness ran native code with no
data limit. Neither holds now, and no limit of either tool sets 20: a
recursive run's stack follows `ulimit -s`, 8 MiB by default
(ADR-2026-11-02-1132), the harness runs native code under a data limit
of 1 GiB (ADR-2026-11-02-2250), and `fir-ref` stops at its fuel. The cap
stays as it is; making deeper runs differential is a decision of its own.
`call-args` passes seven and eight arguments of mixed widths, some on
the stack;
`call-results` calls functions with no result and with one, and
`call-several` with several; `call-symbols` calls
`@"1"` and runs it by that name; `sum` runs the spec's `@sum10`, which
calls `@sum`; and `fuel-call` runs recursion that never ends out of
fuel at the budget that each test sets. `reject/call.toml` holds the
texts of `call` that do not decode, and `reject/validation-call.toml`
those that break its rules of validation: an unknown callee, and
arguments or results that do not match the callee's signature.

The texts of #21 run every op but division at `i128`, on the boundary
bit patterns and on values that cross the 64-bit boundary, such as
`2^64 - 1`, `2^64`, `-2^64` and a value whose halves differ.
`add-i128`, `sub-i128` and `mul-i128` run each op with each set of
flags, and add pairs that carry or borrow out of the low half, and
products whose high half comes from the cross products. `bitwise-i128`,
`icmp-eq-i128`, `icmp-signed-i128`, `icmp-unsigned-i128` and
`select-i128` add values whose halves differ, or whose low halves
compare the other way from their high halves. `shl-i128`, `lshr-i128`
and `ashr-i128` shift by 63, 64, 65 and 127, and by 128 or more, which
gives poison. `zext-i128`, `sext-i128` and `trunc-i128` change widths
to and from `i1`, `i8`, `i16`, `i32` and `i64`. `freeze-i128` freezes
values and poison, and `freeze-xor-i128` runs `xor %f, %f` on a frozen
poison, declared as its one result `0` with a witness. `branch-i128`,
`permute-i128` and `loop-i128` pass `i128` block arguments, and
`call-i128`, `call-args-i128` and `recursion-i128` pass and return
`i128`s across calls, in register pairs and on the stack, in each layout
of ADR-2026-11-03-0108. `tracer-i128` states what `fir-ref` gives for
`const`, `add` and `ret` at `i128`.

The texts of #31 return several values natively, as
[ADR-2026-11-03-0109](../../docs/adrs/2026-11-03-0109-results-return-as-a-system-v-structure.md)
lays them out: one or two in registers, more in a result area that the
caller provides. `several-iN` returns no value, two, three and eight,
passes the results of one call on to others, recurses directly and
mutually returning several values, returns poison in one value and
defined values in the others, and hits UB and runs out of fuel in a
callee that returns several values, at the same seven widths; at `i7`
and `i33` every test is interpreter-only. `several-mixed` returns
results of mixed widths and calls with six or more arguments whose
results go in memory, so that some arguments go on the stack.
`results` and `call-several`, interpreter-only until #31, are
differential.

The texts of #21 that came after #31 return an `i128` among several
results, which goes in the result area at an offset that is a multiple
of 16, low half first. `several-i128` returns an `i128` first, in the
middle, last, and twice, among narrower results, poison in an `i128`
next to defined results and the reverse, and a frozen value twice.
`several-pairs-i128` returns an `i128` next to an `i64` in either order,
and two `i128`s, passes an `i128` result on to other calls, and hits UB
and runs out of fuel in callees that return `i128`s among other results.
`several-args-i128` passes `i128` arguments to calls whose results go in
memory, so that the area's address takes `%rdi` and some of them go on
the stack, and recurses 20 deep returning two `i128`s around an `i64`.

The texts of #22 divide at `i128`, which native code does through a
runtime helper
([ADR-2026-11-03-0415](../../docs/adrs/2026-11-03-0415-the-i128-division-routines-are-system-v-functions.md)).
`div-sdiv-i128`, `div-udiv-i128`, `div-srem-i128` and `div-urem-i128`
run each op on every pair of 13 values of both signs, below and above
`2^64` and near the signed minimum; a pair that is UB in the spec is an
interpreter-only test. `div-sdiv-exact-i128` and `div-udiv-exact-i128`
run `exact` on pairs that divide exactly and pairs that do not, each
with an interpreter-only twin. `poison-div-i128` passes poison to each
op as either operand and as both. `div-calls-i128` returns quotients
and remainders among several results and passes them across calls, and
`div-symbol-i128` names functions after the helper's routines
([ADR-2026-11-03-0414](../../docs/adrs/2026-11-03-0414-the-i128-division-helper-lives-in-the-module-s-object-file.md)).

The texts of #23 fill the cells of the coverage matrix that had no
test. `branch-no-args` runs `br` to blocks that take no arguments, as a
differential test. The interpreter-only tests at the end of `add-i128`,
`sub-i128`, `mul-i128`, `bitwise-i128`, the three `icmp-*-i128`,
`select-i128`, `branch-i128`, `zext-i128`, `sext-i128` and `trunc-i128`
state what `fir-ref` gives at `i128`, and those at the end of
`freeze-i1` to `freeze-i64` what it gives for `freeze` on each choice,
as `freeze-i7` does. `zext-i7`, `sext-i7`, `trunc-i7` and their `i33`
twins also change widths to and from `i128`.
