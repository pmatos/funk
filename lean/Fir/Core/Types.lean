import Fir.Syntax.Dialect

/-!
The core dialect is the small, CPU-shaped dialect that M0 defines. Its types
are the integers `iN` and the reserved type `ptr` (S2, ADR-2026-10-29-2007).
They are one dialect's types, not the whole type system of fir: an extension
dialect brings its own (G0).
-/

namespace Fir.Core

/--
A type of the core dialect.

* `int w` is `iN` with `N = w`: a bitvector of `w` bits. Any width from 1
  to `maxWidth`, 16,777,215, is allowed, as in MLIR; validation rejects `i0`,
  and the text format rejects a wider type (N3). An integer type has no
  sign. Signedness lives on ops (`sdiv` and `udiv`, `icmp slt` and
  `icmp ult`), and one bit pattern is read both ways.
* `ptr` is reserved. M0 gives it no ops, and its values wait for the memory
  model (S3), which is not decided. Validation in M0 rejects every value of
  type `ptr`.
-/
inductive Ty where
  | int (w : Nat)
  | ptr
  deriving Repr, DecidableEq, Inhabited

/-- The widest integer type, `i16777215`: `2^24 - 1` bits, MLIR's limit. -/
def maxWidth : Nat := 2 ^ 24 - 1

end Fir.Core
