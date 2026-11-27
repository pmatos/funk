/-!
Fir compares names, which are strings, numbers and bit vectors by their
decidable equality. Validation and the tests decide equality of names in the kernel,
and each proof that compares them uses only `propext` and `Quot.sound`, so
the instances that give `==` on strings and its lawfulness on numbers must
reduce and must not rest on `Classical.choice`.

Lean v4.36.0 gives `String` and `BitVec w` a linear order package, and
`BEq` on them then resolves to the package's `==`, which the kernel cannot
reduce and whose proofs use `Classical.choice`. Its `LawfulBEq Nat` comes
through the order classes too. This module puts back, at a higher priority,
the instances that Lean v4.35.0 resolved: `==` on strings and bit vectors
from their decidable equality, and the lawfulness of `==` on strings,
numbers and bit vectors from the same. Every module of fir
that does not import another one imports this module, so all of fir sees one
`BEq String`, and a hash map keyed by strings has one type throughout.
-/

namespace Fir

/-- Equality of strings by their decidable equality, as Lean v4.35.0
resolved it, ahead of the order package of Lean v4.36.0. -/
instance (priority := high) instBEqString : BEq String := instBEqOfDecidableEq

/-- `==` on strings is lawful, from their decidable equality. -/
instance (priority := high) instLawfulBEqString : LawfulBEq String := instLawfulBEq

/-- `==` on numbers is lawful, from their decidable equality, ahead of the
order classes of Lean v4.36.0. -/
instance (priority := high) instLawfulBEqNat : LawfulBEq Nat := instLawfulBEq

/-- Equality of bit vectors by their decidable equality, as Lean v4.35.0
resolved it, ahead of the order package of Lean v4.36.0. -/
instance (priority := high) instBEqBitVec {w : Nat} : BEq (BitVec w) := instBEqOfDecidableEq

/-- `==` on bit vectors is lawful, from their decidable equality. -/
instance (priority := high) instLawfulBEqBitVec {w : Nat} : LawfulBEq (BitVec w) := instLawfulBEq

end Fir
