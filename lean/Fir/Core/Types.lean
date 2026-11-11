import Fir.Syntax.Dialect

/-!
The core dialect is the small, CPU-shaped dialect of fir's first milestone,
M0. Its types are the integer types, the float types and the reserved
pointer type (ADR-2026-10-29-2007, ADR-2026-11-09-1549). They are one
dialect's types, not the whole type system of fir: another dialect brings
its own (ADR-2026-10-29-2016).
-/

namespace Fir.Core

/--
A type of the core dialect.

* `int w` is `iN` with `N = w`: a bitvector of `w` bits. Any width from 1
  to `maxWidth`, 16,777,215, is allowed, as in MLIR; validation rejects `i0`,
  and the text format rejects a wider type (N3). An integer type has no
  sign. Signedness lives on ops (`sdiv` and `udiv`, `icmp slt` and
  `icmp ult`), and one bit pattern is read both ways.
* `float e m` is `float<e,m>`, the IEEE 754 binary format with `e` exponent
  bits and `m` explicit mantissa bits: a sign bit, then the exponent, then
  the mantissa, `1 + e + m` bits in all (ADR-2026-11-09-1549). Validation
  accepts `e ≥ 2` and `m ≥ 1`, every format of Lean's float model
  (ADR-2026-11-11-0950). `f16`, `bf16`, `f32`, `f64` and `f128` are
  `float<5,10>`, `float<8,7>`, `float<8,23>`, `float<11,52>` and
  `float<15,112>`.
* `ptr` is reserved. M0 gives it no ops, and its values wait for the memory
  model (S3), which is not decided. Validation in M0 rejects every value of
  type `ptr`.
-/
inductive Ty where
  | int (w : Nat)
  | float (e m : Nat)
  | ptr
  deriving Repr, DecidableEq, Inhabited

/-- The widest integer type, `i16777215`: `2^24 - 1` bits, MLIR's limit. -/
def maxWidth : Nat := 2 ^ 24 - 1

/-- The bits of a value of `float<e,m>`: a sign bit, `e` exponent bits and
`m` mantissa bits. -/
def floatWidth (e m : Nat) : Nat := 1 + e + m

end Fir.Core
