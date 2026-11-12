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
invalid because `the set holds UB (sdiv by zero)`
([testing-and-harness.md](../decisions/testing-and-harness.md#the-invalid-verdict-is-itself-tested)).
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
`ulimit -s`, 8 MiB by default
([x86-64-backend-executable.md](../decisions/x86-64-backend-executable.md#the-runs-stack)).
`recursion-i8`, `recursion-i64` and `recursion-i128` recurse up to 100,000 calls on it,
and their sidecars give the figures. A deeper run reports that it ran
out of stack, and the harness reports its test invalid, not a mismatch
([testing-and-harness.md](../decisions/testing-and-harness.md#a-run-that-outgrows-its-stack)):
`scripts/harness/fixtures/out-of-stack/` checks
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
of [x86-64-backend-abi.md](../decisions/x86-64-backend-abi.md#arguments).
`tracer-i128` states what `fir-ref` gives for
`const`, `add` and `ret` at `i128`, and repeats each run with a defined
result as a differential test.

The texts of #31 return several values natively, as
[ADR-2026-10-30-1232](../adrs/2026-10-30-1232-funk-function-abi.md)
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
([x86-64-backend-lowering.md](../decisions/x86-64-backend-lowering.md#division-at-i128)).
`div-sdiv-i128`, `div-udiv-i128`, `div-srem-i128` and `div-urem-i128`
run each op on every pair of 13 values of both signs, below and above
`2^64` and near the signed minimum; a pair that is UB in the spec is an
interpreter-only test. `div-sdiv-exact-i128` and `div-udiv-exact-i128`
run `exact` on pairs that divide exactly and pairs that do not, each
with an interpreter-only twin. `poison-div-i128` passes poison to each
op as either operand and as both. `div-calls-i128` returns quotients
and remainders among several results and passes them across calls, and
`div-symbol-i128` names functions after the helper's routines
([x86-64-backend-lowering.md](../decisions/x86-64-backend-lowering.md#division-at-i128)).

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
([ADR-2026-10-29-2006](../adrs/2026-10-29-2006-poison-and-freeze.md)).
Until then fir had no poison constant, and a text made poison with an op
whose rule gives it, such as `add nsw` on the signed maximum.
`poison-op-iN` returns it, alone and beside a value, adds it, compares
it with itself, which is poison, selects it on either arm, passes it to
a callee that ignores it, freezes it, and branches on it and divides by
it, which is UB, at `i1`, `i7`, `i8`, `i16`, `i32`, `i33`, `i64` and
`i128`. At the backend's widths the
differential tests run it as native code, which gives zero for it, and
the interpreter-only tests that fill its cells observe the poison
([testing-and-harness-corpus.md](../decisions/testing-and-harness-corpus.md#the-cells-of-poison)).
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

The texts of #229's second stage hold the float types
([ADR-2026-11-09-1549](../adrs/2026-11-09-1549-floating-point-is-strict-ieee-over-generic-formats.md),
[ADR-2026-11-11-0951](../adrs/2026-11-11-0951-a-float-type-is-written-by-its-alias-or-as-float-e-m.md)).
`float-types` passes values of each alias, of formats written
`float(e, m)`, the smallest, `float(2, 1)`, and the widest among them, as
parameters, block arguments, call arguments and results.
`reject/float-types.toml` holds its texts that do not decode, such as
`float(8, 23)`, which is written `f32`, or do not validate, such as
`float(1, 1)`, and ops that take integers at a float type.

The texts of #229's third stage also use float constants and `fcmp`
([ADR-2026-11-11-1438](../adrs/2026-11-11-1438-a-float-constant-is-its-shortest-decimal-or-its-bits-in-hexadecimal.md),
[ADR-2026-11-09-1549](../adrs/2026-11-09-1549-floating-point-is-strict-ieee-over-generic-formats.md)).
A float is spelled as its shortest decimal, as `1.0`, or as its bits in
hexadecimal, as `0x7fc00000`.
`fcmp-ordered-T` runs each of the seven ordered predicates, and
`fcmp-unordered-T` each of the seven unordered ones, at `T`, one of `f16`,
`bf16`, `f32`, `f64` and `f128`, on pairs of hard values: 1 and 2 in both orders, `-0` and `+0`,
the smallest subnormals against a zero, the largest finite values against
the infinities, and NaNs, quiet and signalling, with a payload and with the
sign set, against numbers, infinities, zeros and each other; and on poison
operands. `fconst-T` returns constants of `T`, each NaN's payload and sign
included, and compares a NaN constant with itself. Both are differential
at `f32` and `f64`, which the backend lowers, and interpreter-only at the
other formats, where `scripts/harness/float_ref.py` computed the expected
results apart from Lean; a few interpreter-only tests at `f32` and `f64`
check `fir-ref` against it too. `float-calls` passes `f32` and `f64` to
and from functions as System V does
([x86-64-backend-abi.md](../decisions/x86-64-backend-abi.md#floats-in-sse-registers)):
past the eight SSE registers onto the stack, back in `%xmm0` and `%xmm1`
or in the result area, mixed with integers and an `i128`, through block
arguments, and chosen by an `fcmp`. `float-values-T` passes values of `T`
through `br` and `cond_br` and back from calls with one result and with
several, for the cells of passed and returned values at each format;
it is differential at `f32` and `f64` and interpreter-only at every
format. `float-types` now has interpreter-only tests that pass values of
every format, poison among them.
`reject/float-ops.toml` holds the float constants and `fcmp` texts that
do not decode.

The texts of #231's stage 3a give `ptr` values
([ADR-2026-11-09-1542](../adrs/2026-11-09-1542-memory-is-logical-blocks-in-typed-memories.md),
[ADR-2026-11-11-1709](../adrs/2026-11-11-1709-a-pointer-type-is-written-ptr-or-ptr-n.md)).
`pointer-types` passes values of `ptr`, the default memory's pointer,
through parameters, results, block arguments and a call, mixed with
integers and a float; a run starts with no allocation, so each pointer
argument is poison, and every test is interpreter-only, since the backend
does not lower pointers yet. `reject/pointer-types.toml` holds the pointer
types that do not decode, such as `ptr(0)`, which is written `ptr`, those
that do not validate, such as `ptr(1)`, a memory that no module has yet,
and pointers passed where a pointer of another memory or an integer is
expected. The texts that relied on `ptr` being invalid name `ptr(1)` or
another memory now.

The texts of #229's fourth stage also use the float arithmetic `fadd`,
`fsub`, `fmul`, `fdiv`, `fneg`, `fabs`, `sqrt` and `fma`
([ADR-2026-11-09-1549](../adrs/2026-11-09-1549-floating-point-is-strict-ieee-over-generic-formats.md),
[ADR-2026-11-11-1801](../adrs/2026-11-11-1801-a-rounding-op-is-written-with-round-rne.md)).
`float-binary-T` runs `fadd`, `fsub`, `fmul` and `fdiv`, and
`float-unary-fma-T` runs `fneg`, `fabs`, `sqrt` and `fma`, at `T`, one of
`f16`, `bf16`, `f32`, `f64` and `f128`, on the hard inputs: results
halfway between two floats, subnormals, `-0`, overflow to infinity and
NaN operands, `fsub` and `fdiv` in both operand orders, and a poison
operand. `scripts/harness/float_arith_cases.py` writes them, with each
expected result that `scripts/harness/float_ref.py` computes
([testing-and-harness-floats.md](../decisions/testing-and-harness-floats.md#the-arithmetic-corpus)).
A result that is not a NaN is differential at `f32` and `f64` and
interpreter-only at every format; a NaN result is interpreter-only, with
a choice that names the NaN, until #219. `reject/float-arith.toml` holds
the texts of these ops that do not decode, such as `fadd` without
`round(rne)` or with `round(rtz)`, and one at a format that validation
rejects.

The texts of #241's first stage also use the bit cast `bitcast`
([ADR-2026-11-09-1549](../adrs/2026-11-09-1549-floating-point-is-strict-ieee-over-generic-formats.md)).
`float-bitcast-T` casts a value of `T`, one of `f16`, `bf16`, `f32`,
`f64` and `f128`, to the integer of its width and back, on zeros of both
signs, subnormals, the smallest normal, one, the largest finite values,
infinities and NaNs with payloads and either sign, and on poison. Each
result is its operand's bits, so every case is differential at `f32` and
`f64`, NaNs included, and interpreter-only at every format.
`scripts/harness/float_bitcast_cases.py` writes them
([testing-and-harness-floats.md](../decisions/testing-and-harness-floats.md#the-bit-cast-corpus)).
`reject/float-bitcast.toml` holds the bit casts that do not decode, such
as an integer of another width, two floats or two integers, and an
attribute, and two at formats that validation rejects.

The texts of #310 also use the remainders `frem`, IEEE 754's, and `fmod`,
C's ([semantics-floats.md](../decisions/semantics-floats.md#the-remainders)).
`float-rem-T` runs both at each `T`, on the hard inputs of
`scripts/harness/float_rem_cases.py`: quotients halfway between two
integers, subnormals, `-0`, operands far apart, infinities and NaN
operands, each in both operand orders, and a poison operand, as
`float_arith_cases.py` writes them. `reject/float-arith.toml` holds
`frem round(rne)`, which does not decode, since a remainder does not
round.
