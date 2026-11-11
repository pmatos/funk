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
refinement, and the corpus holds them. No core op takes or gives a float yet,
and a float type has no constants, so `fir-ref run` takes no float argument and
the naive backend reports a float parameter or result as a diagnostic. The
check of Lean's float model at other formats is in
`lean/FirTest/FloatModel.lean`, and the exact-rational reference that computed
its expected bit patterns is `scripts/harness/float_ref.py`.
