import Fir.Core.Rounding

/-!
The attributes that core ops carry: the wrap flags of `add`, `sub` and
`mul`, the predicates of the integer and float comparisons, the fast-math
flags of float ops, the float ops of two operands and of one, with the
rounding mode of each op that rounds, and the kinds of an op that carries
units across memory, a copy or a move. The section on core ops uses them.
-/

namespace Fir.Core

/--
The flags of `add`, `sub` and `mul`. Each one is a promise about the
operands; when it is broken, the result is poison.

* `nuw` (no unsigned wrap): the operands, read as unsigned integers, give a
  result that fits in `N` bits.
* `nsw` (no signed wrap): the operands, read as two's-complement signed
  integers, give a result that fits in `N` bits.
-/
structure WrapFlags where
  nuw : Bool := false
  nsw : Bool := false
  deriving Repr, DecidableEq, Inhabited

/--
The predicate of an integer comparison. `eq` and `ne` compare bits. The `s`
predicates read the operands as signed integers, the `u` predicates as
unsigned: `lt` is less than, `le` less or equal, `gt` greater than and `ge`
greater or equal.
-/
inductive Pred where
  | eq | ne | slt | sle | sgt | sge | ult | ule | ugt | uge
  deriving Repr, DecidableEq, Inhabited

/--
The predicate of a float comparison, as LLVM names it. An `o` predicate is
ordered: it is false when either operand is a NaN. A `u` predicate is
unordered: it is true when either operand is a NaN. Otherwise each compares
the numbers that the operands encode, so `-0` equals `+0`: `eq` is equal,
`ne` not equal, `lt` less than, `le` less or equal, `gt` greater than and
`ge` greater or equal. `ord` holds when neither operand is a NaN, and `uno`
when either is (ADR-2026-11-09-1549).
-/
inductive FPred where
  | oeq | one | olt | ole | ogt | oge | ord
  | ueq | une | ult | ule | ugt | uge | uno
  deriving Repr, DecidableEq, Inhabited

/--
The fast-math flags of a float op (ADR-2026-11-09-1549). Each of the first
three is a promise about the op's operands or result:

* `nnan` (no NaNs): no operand and no result is a NaN. A NaN operand or
  result makes the result poison.
* `ninf` (no infinities): no operand and no result is an infinity. An
  infinite operand or result makes the result poison.
* `nsz` (no signed zeros): the sign of a zero result does not matter. A
  zero result is `+0` or `-0`, a free choice.

`contract` and `reassoc` are reserved words. They are permissions for
passes, not meanings of an op, and M2's optimizer decides them, so
validation rejects an op that carries either, and the rules ignore them.
-/
structure FastMath where
  nnan : Bool := false
  ninf : Bool := false
  nsz : Bool := false
  contract : Bool := false
  reassoc : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Whether the flags hold a reserved word, `contract` or `reassoc`. -/
def FastMath.Reserved (fl : FastMath) : Bool := fl.contract || fl.reassoc

/--
A float op of two operands (ADR-2026-11-09-1549): `fadd` adds, `fsub`
subtracts the second operand from the first, `fmul` multiplies and `fdiv`
divides the first by the second, each rounded with its mode `r`. `frem`
and `fmod` give the remainder of the first by the second, `x - n * y`,
which is exact, so they do not round and have no mode: `frem`'s `n` is
the quotient rounded to nearest, ties to even, IEEE 754's remainder, and
`fmod`'s is the quotient truncated, C's `fmod` and LLVM's `frem` (#310).
-/
inductive FBin where
  | fadd (r : RoundingMode) | fsub (r : RoundingMode) | fmul (r : RoundingMode)
  | fdiv (r : RoundingMode) | frem | fmod
  deriving Repr, DecidableEq, Inhabited

/--
A float op of one operand (ADR-2026-11-09-1549): `fneg` negates, `fabs`
gives the absolute value, and `sqrt` the square root, rounded with its
mode `r`. Only `sqrt` rounds, so only it has a mode: a negation or an
absolute value is a float of the format.
-/
inductive FUnary where
  | fneg | fabs | sqrt (r : RoundingMode)
  deriving Repr, DecidableEq, Inhabited

/--
What an op that carries units across memory does with its two ranges
(ADR-2026-11-09-1551): `copy`, written `memcpy`, asks that they be equal
or disjoint, and `move`, written `memmove`, lets them overlap.
-/
inductive CopyKind where
  | copy | move
  deriving Repr, DecidableEq, Inhabited

end Fir.Core
