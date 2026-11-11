# Current decisions: semantics, floating point

This page continues semantics-m1-design.md. It says what the ADRs decide about
floating point in fir, and what holds in the spec and the tools today. It
summarizes the ADRs it cites and does not replace them. When this page and an
ADR disagree, the page is wrong (ADR-2026-11-09-1610).

## The design

Floating point is one type family, `float<e,m>`, with `e` exponent bits and `m`
explicit mantissa bits. The usual names are aliases: `f16`, `bf16`, `f32`, `f64`
and `f128`. The spec and `fir-ref` handle every IEEE-shaped format. A format
that is not IEEE-shaped, such as fp8 e4m3fn, is left to dialects
(ADR-2026-11-09-1549).

The semantics is strict IEEE 754. Denormals are honoured. Flush-to-zero is an
explicit target attribute. When an op's IEEE result is a NaN, fir chooses any
NaN bit pattern of the format, so payload and sign are nondeterministic. #219
decides how `fir-ref` and the harness handle that choice (ADR-2026-11-09-1549).

Every rounding op carries `round = rne`. Round to nearest even is the only value
M1 accepts (ADR-2026-11-09-1549).

The fast-math flags are (ADR-2026-11-09-1549):

- `nnan`: a NaN operand or result makes the result poison.
- `ninf`: an infinite operand or result makes the result poison.
- `nsz`: the sign of a zero result is a free choice.
- `contract` and `reassoc` are reserved words that the verifier rejects. They
  are permissions for passes, not meanings of an op, and M2's optimizer decides
  them.

The spec defines fir's float ops on Lean's model, with a layer that adds the NaN
choice. It defines the conversions between widths itself. Facts it needs are
proved here, or checked with `decide` and `bv_decide`. Before relying on the
model, the implementation confirms that each operation works for a format other
than binary32 and binary64 (ADR-2026-11-09-1549).

The naive backend lowers `f32` and `f64` with SSE in M1, and reports any other
format as a diagnostic. A native result in a format it does not lower is judged
by `fir-ref` alone (ADR-2026-11-09-1549).

## The formats

The core accepts `float<e,m>` with `e >= 2` and `m >= 1`: every format of Lean's
float model, `float<2,1>` the smallest. Validation rejects a format with fewer
bits, as it rejects `i0`. A value of `float<e,m>` has `1 + e + m` bits, and a
format wider than 16,777,215 bits in all, the widest integer type, does not
decode (ADR-2026-11-11-0950).

A value of `float<e,m>` is its raw bit pattern or poison. Values refine as
integers do: poison is refined by every value of the type, and a bit pattern
only by itself. Which bits an op gives, a NaN's among them, is the op's rule
(ADR-2026-11-11-0950).

A format with an alias is written by it, and every other format as
`float(e, m)`, the grammar's applied form. So `float(8, 23)` does not decode:
`f32` writes it (ADR-2026-11-11-0951). The text-format page says more.

## What holds today

#229 builds floating point in stages. Today the spec, `fir-ref`, the Rust IR,
parser, printer and verifier have the float types, their values and their
refinement, and the corpus holds them. They also have these float ops:

- A float constant is `const` at a float type, written as its shortest
  decimal that reads back, such as `1.0` or `0.1`, or else as `0x` and its
  bits, such as `0x7fc00000`. Every bit pattern, each NaN payload and sign
  included, has one spelling (ADR-2026-11-11-1438). It is pure.
- `fcmp` compares two floats of one format with one of fourteen predicates,
  ordered or unordered, and gives an `i1`. The spec unpacks both operands and
  compares them with Lean's model, `UnpackedFloat.compare`. It is pure, never
  UB, and never gives a NaN, and a poison operand gives poison
  (ADR-2026-11-11-1139).
- The arithmetic: `fadd`, `fsub`, `fmul`, `fdiv`, `fneg`, `fabs`, `sqrt` and
  `fma`, on values of one format. Each runs Lean's model: it unpacks its
  operands, runs the model's operation, rounded to nearest even, and packs the
  result. When the model's result is a NaN, the op chooses `m + 1` bits, a sign
  and a mantissa, and gives that NaN; a zero mantissa stands for the quiet NaN.
  So a NaN result is any NaN of the format. `fneg` and `fabs` of a NaN are any
  NaN too. Each op is pure and never UB, and a poison operand gives poison. A
  format that validation rejects gives a chosen NaN, so that the rules are
  total (ADR-2026-11-11-1800). Each op that rounds is written with
  `round(rne)`, and `fneg` and `fabs` with no attribute (ADR-2026-11-11-1801).
  The spec's section on float arithmetic says which parts come from the model
  and which are fir's own. `frem` is not built: the model has no remainder.

`fir-ref run` takes float arguments and prints float results in that spelling,
and takes `poison` at a float type. A NaN result makes a choice, so scripted
mode needs `--choices` for it, and exhaustive mode at `f32` and `f64` passes its
budget; #219 decides how `fir-ref` and the harness judge a NaN result. The naive
backend lowers `f32` and `f64`: it passes and returns them in SSE registers as
System V does, and lowers the constants and `fcmp` (ADR-2026-11-11-1140) and
the arithmetic, with SSE2 and, for `fma`, a routine of a runtime helper
(ADR-2026-11-11-1802). It reports every other format as a diagnostic where its
value is defined. The corpus runs every predicate and the constants
differentially at `f32` and `f64`, and on `fir-ref` against
`scripts/harness/float_ref.py` at `f16`, `bf16` and `f128`, on zeros of both
signs, subnormals, the largest finite values, infinities and NaNs. It runs the
arithmetic on the hard inputs of every op, at every aliased format, with each
result that is not a NaN differential at `f32` and `f64`, and each NaN result
on `fir-ref` with a choice (ADR-2026-11-11-1803).

`poison`, `select` and `freeze` take no float yet. The lawful and effect
theorems of the core depend on `Classical.choice`, since Lean's
`UnpackedFloat.unpack` does; the axiom check allows it (ADR-2026-10-30-1452).

The check of Lean's float model at other formats is in
`lean/FirTest/FloatModel.lean`, and the exact-rational reference that computed
its expected bit patterns is `scripts/harness/float_ref.py`.
