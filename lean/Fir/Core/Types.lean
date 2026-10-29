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

* `int w` is `iN` with `N = w`: a bitvector of `w` bits. Any width `w ≥ 1`
  is allowed; validation rejects `i0`. An integer type has no sign.
  Signedness lives on ops (`sdiv` and `udiv`, `icmp.slt` and `icmp.ult`), and
  one bit pattern is read both ways.
* `ptr` is reserved. M0 gives it no ops, and its values wait for the memory
  model (S3), which is not decided. Validation in M0 rejects every value of
  type `ptr`.
-/
inductive Ty where
  | int (w : Nat)
  | ptr
  deriving Repr, DecidableEq, Inhabited

end Fir.Core
