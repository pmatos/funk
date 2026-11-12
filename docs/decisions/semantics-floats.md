# Current decisions: semantics, floating point

This page continues semantics-m1-design.md. It says what the ADRs decide about
floating point in fir, and what holds in the spec and the tools today. It is the
record: when this page and an ADR disagree, the page wins, and the ADR is fixed
or deleted (ADR-2026-11-09-1610). ADR-2026-11-09-1549 holds the direction
decision.

## The design

The human ruled the design on 2026-11-09, on #203 (ADR-2026-11-09-1549).

Floating point is one type family, `float<e,m>`, with `e` exponent bits and `m`
explicit mantissa bits. The usual names are aliases: `f16`, `bf16`, `f32`, `f64`
and `f128`. The spec and `fir-ref` handle every IEEE-shaped format. A format
that is not IEEE-shaped, such as fp8 e4m3fn, which has no infinities, is left to
dialects, so NPU and TPU formats need no change to the core
(ADR-2026-11-09-1549).

The semantics is strict IEEE 754. Denormals are honoured. Flush-to-zero is an
explicit target attribute. When an op's IEEE result is a NaN, fir chooses any
NaN bit pattern of the format, so payload and sign are nondeterministic. #219
decides how `fir-ref` and the harness handle that choice (ADR-2026-11-09-1549).

Every rounding op carries `round = rne`. Round to nearest even is the only value
M1 accepts (ADR-2026-11-09-1549). Whether the verifier or the reader rejects
another rounding mode is an open question for the human, raised on #229
on 2026-11-11; today the reader rejects it (ADR-2026-11-11-1801).

The fast-math flags are (ADR-2026-11-09-1549):

- `nnan`: a NaN operand or result makes the result poison.
- `ninf`: an infinite operand or result makes the result poison.
- `nsz`: the sign of a zero result is a free choice.
- `contract` and `reassoc` are reserved words that the verifier rejects. They
  are permissions for passes, not meanings of an op, and M2's optimizer decides
  them.

Rejected: only `f32` and `f64`, with all five flags. Other formats would need a
format change later, and two flags would ship without a sound meaning. Rejected
too: strict `f32` and `f64` with no flags and no rounding attribute, which drops
the hook for other rounding modes and fails G0's point on formats.

The spec defines fir's float ops on Lean's model, with a layer that adds the NaN
choice. Lean v4.35.0 models its floats in its logic
(`src/Init/Data/Float/Model/` of the Lean sources): the operations take a
format of any exponent and mantissa width, round to nearest even, and have one
canonical NaN with no payload or sign. The spec defines the conversions between
widths itself, since Lean leaves them opaque. Facts it needs are proved here, or
checked with `decide` and `bv_decide`. Before relying on the model, the
implementation confirms that each operation works for a format other than
binary32 and binary64 (ADR-2026-11-09-1549). The spec writes no IEEE arithmetic
of its own; fir's own parts are the NaN choice, poison and the rejected formats,
and the spec's section on float arithmetic lists them.

The naive backend lowers `f32` and `f64` with SSE in M1, and reports any other
format as a diagnostic. A native result in a format it does not lower is judged
by `fir-ref` alone (ADR-2026-11-09-1549).

## The formats

The core accepts `float<e,m>` with `e >= 2` and `m >= 1`: every format of Lean's
float model, `float<2,1>` the smallest, which the corpus checks. The human ruled
this on 2026-11-11, on #229. With `m = 1` the one mantissa bit of a NaN is its
quiet bit, so the format has no signalling NaN, and fir never tells signalling
NaNs from quiet ones. Rejected: require `m >= 2` and leave `float<e,1>` to
dialects. Validation rejects a format with fewer bits, as it rejects `i0`; such
a type still decodes, so the text reads it and the verifier names it. A value of
`float<e,m>` has `1 + e + m` bits, and a format wider than 16,777,215 bits in
all, the widest integer type, does not decode (ADR-2026-11-09-1549,
ADR-2026-10-29-2007). A dialect that needs a format with fewer bits, or one that
is not IEEE-shaped, brings its own type.

A value of `float<e,m>` is its raw bit pattern or poison. Values refine as
integers do: poison is refined by every value of the type, and a bit pattern
only by itself, so two NaNs with different bits are different values. Which
bits an op gives, a NaN's among them, is the op's rule (ADR-2026-11-09-1549).

A format with an alias is written by it, and every other format as
`float(e, m)`, the grammar's applied form. So `float(8, 23)` does not decode:
`f32` writes it (ADR-2026-11-11-0951). The text-format page says more.

## The comparison

`%r: i1 = fcmp P %a, %b` takes two values of one float type and gives an `i1`.
`P` is one of fourteen predicates, LLVM's names: `oeq`, `one`, `olt`, `ole`,
`ogt`, `oge`, `ord`, `ueq`, `une`, `ult`, `ule`, `ugt`, `uge` and `uno`
(ADR-2026-11-09-1549). It follows IEEE 754 §5.11, which compares the numbers
that two floats encode: `-0` equals `+0`, and a NaN is unordered with
everything, itself included.

- The spec unpacks both operands with Lean's model and compares them with
  `UnpackedFloat.compare`, which gives `none` for an unordered pair. An `o`
  predicate is false on an unordered pair and a `u` predicate true. Otherwise
  `eq`, `ne`, `lt`, `le`, `gt` and `ge` say how the two numbers compare. `ord`
  holds when the pair is ordered, and `uno` when it is not.
- A format that the model does not accept, which validation rejects, has every
  pair unordered, so that the rule is total.
- `fcmp` never gives a NaN and is never UB. A poison operand gives a poison
  result. It is pure.
- LLVM's `false` and `true` predicates are not predicates of `fcmp`: they do
  not look at their operands, and `const false` and `const true` write them.
  Rejected: all sixteen of LLVM's predicates, since two compare nothing and
  each would be one more case in every layer.

Rejected: compare the bits directly, which would be a second definition of the
order beside the model.

## The arithmetic

`fadd`, `fsub`, `fmul` and `fdiv` take two values of one float type, `fneg`,
`fabs` and `sqrt` one, and `fma` three; each gives one value of that type. In
the spec they are three op instances: `fbin o e m`, `funary o e m` and
`fma e m` (ADR-2026-11-09-1549).

- On defined operands, each op unpacks them with `UnpackedFloat.unpack`, runs
  the model's operation (`add`, `sub`, `mul`, `div`, `neg`, `abs`, `sqrt` or
  `fma`), rounded to nearest even, and, when the result is not a NaN, packs it
  with `UnpackedFloat.pack`.
- When the model's result is a NaN, the op chooses `m + 1` bits: the top one
  is the sign and the low `m` are the mantissa, with the exponent all ones. A
  mantissa of zeros would be an infinity, so it stands for the quiet NaN, with
  only the top mantissa bit set. So every NaN of the format may be the result,
  quiet or signalling, with any payload and either sign, and nothing else. The
  op chooses only when the result is a NaN, through the choice effect, as
  `freeze` does (`anyNaN` in `lean/Fir/Core/FloatArith.lean`). Rejected:
  choose all `1 + e + m` bits and keep them only when they are a NaN, which
  needs a fallback for the bits that are not, and a choice of more bits, which
  exhaustive runs pay for.
- `fneg` and `fabs` go through the model too, so their result on a NaN is any
  NaN. Rejected: `fneg` and `fabs` as bit operations, flipping or clearing the
  sign bit, as IEEE 754 and LLVM define them. The bit operations refine the
  model's rule, and the backend uses them.
- A poison operand gives a poison result. No op is ever UB: division by zero
  gives an infinity or a NaN, and M1 has no floating-point exceptions.
- Each op is pure. A NaN is a defined value, so on defined operands the result
  is defined. May produce poison comes with the fast-math flags (#242).
- A format that validation rejects gives a chosen NaN, as above, so that the
  rules are total.

Each op that rounds is written with `round(rne)`, and `fneg` and `fabs` with no
attribute (ADR-2026-11-11-1801).

## The remainders

`%q: f64 = frem %a, %b` and `%q: f64 = fmod %a, %b` take two values of one
float type and give one of it: `x - n * y`, with an integer `n` near the
quotient `x / y`. The human ruled on 2026-11-12, on #310, that fir follows IEEE
754 here, and builds C's `fmod` beside it:

- `frem` is IEEE 754's remainder (§5.3.1): `n` is `x / y` rounded to nearest,
  ties to even. `5.5 frem 2.0` is `-0.5`, and `3.0 frem 2.0` is `-1.0`.
- `fmod` is C's `fmod`: `n` is `x / y` truncated toward zero, so the result has
  the sign of `x`. `5.5 fmod 2.0` is `1.5`. LLVM's `frem` is this op, so fir's
  `frem` is not LLVM's `frem`.

Rejected: `frem` as LLVM's, the truncated remainder, which is not the remainder
IEEE 754 defines; and `frem` alone, which leaves the C operation that LLVM
programs use unwritable.

- Neither rounds. The remainder of two finite floats is a multiple of the
  smaller of their quanta and no larger than `|y|`, so the format holds it
  exactly. Neither carries `round(rne)`, as `fneg` and `fabs` do not
  (ADR-2026-11-11-1801).
- The special cases follow IEEE 754 for `frem` and C's Annex F for `fmod`,
  which agree: `y = 0`, an infinite `x` or a NaN operand gives a NaN, which
  is any NaN as above; a finite `x` with an infinite `y` gives `x`; and a zero
  result, a zero `x` included, has the sign of `x`.
- Lean's model has no remainder, so the spec defines it on the model's
  numbers, `remainder` in `lean/Fir/Core/FloatRem.lean`: it writes both
  operands at the smaller exponent as whole numbers, takes their quotient and
  remainder, and moves the remainder by `|y|` for `frem` past half of `|y|`, or
  at half with an odd quotient. The model's `normalize` writes the result,
  which it never rounds. Everything else, the NaN, poison and the rejected
  formats, is the rule of the arithmetic above: in the spec, `frem` and `fmod`
  are two ops of `fbin o e m`. Each is pure and never UB.

## The conversions

#241 adds the conversions of ADR-2026-11-09-1549 in four stages, as its stage
plan says: bit casts, then `fpext` and `fptrunc`, then integer to float, then
float to integer.

Open questions to the human, raised on 2026-11-12 on #241 and not yet ruled.
How float to integer rounds: #241 gives `round = rne` to integer to float and
to `fptrunc`, and nothing to `fptosi` and `fptoui`, which in C, LLVM and SSE's
`cvttss2si` truncate toward zero, so `2.7` gives `2` and `-2.7` gives `-2`;
stage 4 waits on it. Which op converts between two formats where neither holds
the other, such as `bf16` and `f16`: the stage plan proposes `fpext` only where
the target holds every value of the source, and `fptrunc`, rounding to nearest
even, for every other pair; stage 2 waits on that pair.

`bitcast` reads the same bits as another type of the same width. From
`float<e,m>` it gives an `iN` with `N = 1 + e + m`, and from that `iN` it
gives a `float<e,m>`; the spec has one op instance for each direction,
`toBits e m` and `ofBits e m`, with one rule, `bitcastValue`, which keeps
every bit (`lean/Fir/Core/FloatBitcast.lean`).

- A value of a float type is its bit pattern, so the rule changes no bit. It
  reads no number: Lean's model takes no part, nothing rounds, and no NaN is
  chosen. A NaN's sign and payload come through as they are, both ways, and
  every bit pattern of `iN` is a float, a signalling NaN's included. This is
  IEEE 754's view of an encoding as its bits, and LLVM's `bitcast`.
- A poison operand gives poison, and a value gives a value. It is never UB,
  and it is pure.
- Its widths must match: an op whose integer has another width, or that
  casts between two floats or two integers, does not decode, so validation
  has no rule of its own for it. Rejected: bit casts between two float
  formats of one width, such as `f16` and `bf16`, which #241 does not ask
  for.

## What holds today

#229 builds floating point in stages. Today the spec, `fir-ref`, the Rust IR,
parser, printer and verifier have the float types, their values and their
refinement, and the corpus holds them. They also have the comparison and the
arithmetic above, the remainders of #310, float constants, and `bitcast`
between a float and the integer of its width. A float constant is `const` at a
float type, written as its shortest decimal that reads back, such as `1.0` or `0.1`,
or else as `0x` and its bits, such as `0x7fc00000`. Every bit pattern, each NaN
payload and sign included, has one spelling (ADR-2026-11-11-1438). It is pure.

`fir-ref run` takes float arguments and prints float results in that spelling,
and takes `poison` at a float type. It gives one result, with no choice, for
every result that is not a NaN, so `funk` and `fir-ref` compare those
differentially. A NaN result makes a choice, so scripted mode needs `--choices`
for it, and exhaustive mode at `f32` and `f64` passes its 16-bit budget; #219
decides how `fir-ref` and the harness judge a NaN result. `fcmp`'s result is
never a NaN, so it is differential already. The naive backend lowers `f32` and
`f64`: it passes and returns them in SSE registers as System V does
([x86-64-backend-abi.md](x86-64-backend-abi.md#floats-in-sse-registers)), and
lowers the constants, `fcmp` and the arithmetic, with SSE2 and, for `fma`, a
routine of a runtime helper, the remainders with routines of another that
run the x87 unit's `fprem1` and `fprem`, and `bitcast` as a copy of a slot
([x86-64-backend-lowering.md](x86-64-backend-lowering.md)). It reports every
other format as a diagnostic where its value is defined. The corpus runs every
predicate and the constants differentially at `f32` and `f64`, and on `fir-ref`
against `scripts/harness/float_ref.py` at `f16`, `bf16` and `f128`, on zeros of
both signs, subnormals, the largest finite values, infinities and NaNs. It runs
the arithmetic and the remainders on the hard inputs of every op, at every
aliased format, with
each result that is not a NaN differential at `f32` and `f64`, and each NaN
result on `fir-ref` with a choice
([testing-and-harness-floats.md](testing-and-harness-floats.md#the-arithmetic-corpus)).
It runs `bitcast` both ways at every aliased format, on the same edges, each
case differential at `f32` and `f64`, NaNs included
([testing-and-harness-floats.md](testing-and-harness-floats.md#the-bit-cast-corpus)).

`poison`, `select` and `freeze` take no float yet. The lawful and effect
theorems of the core depend on `Classical.choice`, since Lean's
`UnpackedFloat.unpack` does; the axiom check allows it (ADR-2026-10-30-1452).

The check of Lean's float model at other formats is in
`lean/FirTest/FloatModel.lean`, and the exact-rational reference that computed
its expected bit patterns is `scripts/harness/float_ref.py`.
