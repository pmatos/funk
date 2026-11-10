# What the corpus texts test

This page lists the texts of the fir test corpus,
[`tests/fir/`](../../tests/fir/README.md), family by family, in the order
their tickets added them, and says what each one tests. The corpus README
says how a text and its tests are written. Each text's sidecar says the
same in more detail. Paths are relative to `tests/fir/`, but for those of
the harness, under `scripts/harness/`.

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
recurses as deep as native code's stack allows; fir has no depth limit
of its own (ADR-2026-10-30-1549). A recursive run's stack follows
`ulimit -s`, 8 MiB by default (ADR-2026-11-02-1132). `recursion-i8`,
`recursion-i64` and `recursion-i128` recurse up to 100,000 calls on it,
and their sidecars give the figures. A deeper run reports that it ran
out of stack, and the harness reports its test invalid, not a mismatch
(ADR-2026-11-09-1602): `scripts/harness/fixtures/out-of-stack/` checks
that verdict.
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
`const`, `add` and `ret` at `i128`, and repeats each run with a defined
result as a differential test.

The texts of #31 return several values natively, as
[ADR-2026-11-03-0109](../adrs/2026-11-03-0109-results-return-as-a-system-v-structure.md)
lays them out: one or two in registers, more in a result area that the
caller provides. `several-iN` returns no value, two, three and eight,
passes the results of one call on to others, recurses directly and
mutually returning several values, returns poison in one value and
defined values in the others, and hits UB and runs out of fuel in a
callee that returns several values, at the same seven widths; at `i7`
and `i33` every test is interpreter-only. `several-mixed` returns
results of mixed widths and calls with six or more arguments whose
results go in memory, so that some arguments go on the stack.
`results` and `call-several` were interpreter-only before #31 and are
differential now.

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
([ADR-2026-11-03-0415](../adrs/2026-11-03-0415-the-i128-division-routines-are-system-v-functions.md)).
`div-sdiv-i128`, `div-udiv-i128`, `div-srem-i128` and `div-urem-i128`
run each op on every pair of 13 values of both signs, below and above
`2^64` and near the signed minimum; a pair that is UB in the spec is an
interpreter-only test. `div-sdiv-exact-i128` and `div-udiv-exact-i128`
run `exact` on pairs that divide exactly and pairs that do not, each
with an interpreter-only twin. `poison-div-i128` passes poison to each
op as either operand and as both. `div-calls-i128` returns quotients
and remainders among several results and passes them across calls, and
`div-symbol-i128` names functions after the helper's routines
([ADR-2026-11-03-0414](../adrs/2026-11-03-0414-the-i128-division-helper-lives-in-the-module-s-object-file.md)).

The texts of #23 fill the cells of the coverage matrix that had no
test. `branch-no-args` runs `br` to blocks that take no arguments, as a
differential test. The interpreter-only tests at the end of `add-i128`,
`sub-i128`, `mul-i128`, `bitwise-i128`, the three `icmp-*-i128`,
`select-i128`, `branch-i128`, `zext-i128`, `sext-i128` and `trunc-i128`
state what `fir-ref` gives at `i128`, and those at the end of
`freeze-i1` to `freeze-i64` what it gives for `freeze` on each choice,
as `freeze-i7` does. `zext-i7`, `sext-i7`, `trunc-i7` and their `i33`
twins also change widths to and from `i128`.

The texts of #122 also use `poison`, the constant whose result is poison
([ADR-2026-11-03-1615](../adrs/2026-11-03-1615-the-core-dialect-writes-poison-with-a-constant-op-that-propagates-poison.md)).
Until then fir had no poison constant, and a text made poison with an op
whose rule gives it, such as `add nsw` on the signed maximum.
`poison-op-iN` returns it, alone and beside a value, adds it, compares
it with itself, which is poison, selects it on either arm, passes it to
a callee that ignores it, freezes it, and branches on it and divides by
it, which is UB, at `i1`, `i7`, `i8`, `i16`, `i32`, `i33`, `i64` and
`i128`. At the backend's widths the
differential tests run it as native code, which gives zero for it, and
the interpreter-only tests that fill its cells observe the poison
([ADR-2026-11-03-1618](../adrs/2026-11-03-1618-poison-s-differential-cells-are-filled-by-native-runs-and-its-interpreter-only-cells-by-observing-it.md)).
`reject/poison.toml` holds its texts that do not decode.

The tests of #123 pass `poison` as an argument. `poison-arg-iN` runs
arithmetic, bitwise ops, shifts, `icmp`, `select`, width changes,
division, `br`, `cond_br`, a loop, calls, a recursion, several results
and `freeze` on poison arguments, at the eight widths above.

The texts of #228 also use `unreachable`, the terminator that is
immediate UB when a run reaches it (ADR-2026-11-09-1548).
`unreachable` guards a value at each width of the backend, with the
trap after the block that returns and before it, and its differential
tests take the branch that passes it by, while its interpreter-only
tests reach it. It also holds a function whose last call never returns,
which runs out of fuel without reaching `unreachable`, and a caller of a
function that is all `unreachable`, which is UB of the caller.
`reject/unreachable.toml` holds its texts that do not decode or do not
validate: with an attribute, an operand, a result or a successor, with
an op after it, and with a block that only its place could reach.
