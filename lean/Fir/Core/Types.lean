import Fir.Syntax.Dialect

/-!
The core dialect is the small, CPU-shaped dialect of fir's first milestone,
M0. Its types are the integer types, the float types and the pointer types,
one for each memory (ADR-2026-10-29-2007, ADR-2026-11-09-1549,
ADR-2026-11-09-1542). They are one
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
* `ptr n` is `ptr<N>` with `N = n`: a pointer into the memory `n`
  (ADR-2026-11-09-1542). The core's `ptr` is `ptr<0>`, the pointer of the
  default memory, which every module has. A pointer of one memory is never
  a pointer of another: `ptr<0>` and `ptr<1>` are different types.
-/
inductive Ty where
  | int (w : Nat)
  | float (e m : Nat)
  | ptr (n : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- The widest integer type, `i16777215`: `2^24 - 1` bits, MLIR's limit. -/
def maxWidth : Nat := 2 ^ 24 - 1

/-- The highest memory number that a pointer type may name, `2^24 - 1`, as
LLVM bounds its address spaces. -/
def maxMemory : Nat := 2 ^ 24 - 1

/-- The bits of a value of `float<e,m>`: a sign bit, `e` exponent bits and
`m` mantissa bits. -/
def floatWidth (e m : Nat) : Nat := 1 + e + m

end Fir.Core
