import Fir.Core.Arith

/-!
# Subtraction, multiplication and the wrap flags

Ticket #14 gives `sub` and `mul` their rules, and `add`, `sub` and `mul`
their flags. Without flags, each op gives its exact result modulo `2^N`:
it wraps, as two's complement does, and it is never UB. A poison operand
gives poison: the three ops propagate poison (ADR-2026-10-30-0818).

A flag is a promise about the exact result, and a broken promise gives
poison, not UB (S1, ADR-2026-10-29-2006):

* `nuw`: the operands, read as unsigned integers, give an exact result
  that fits in `N` bits, from `0` to `2^N - 1`. A sum that carries out, a
  difference below zero and a product of `2^N` or more break it.
* `nsw`: the operands, read as two's-complement signed integers, give an
  exact result that fits in `N` bits, from `-2^(N-1)` to `2^(N-1) - 1`.

The tests are Lean's own, `BitVec.uaddOverflow` and its five siblings,
which compute the exact result as a natural number or an integer. At `i1`
the signed values are `0` and `-1`, written `false` and `true`, so
`add nsw true, true`, `sub nsw false, true` and `mul nsw true, true` give
poison: their exact results, `-2`, `1` and `1`, do not fit. With both flags, a result is poison when
either promise is broken. One rule, `wrapValues`, serves all three ops at
every width: it takes the op's result without flags and the op's two
tests.
-/

namespace Fir.Core

/-- `sub` without flags: the difference modulo `2^N` of two values, and
poison when either operand is poison. -/
def subValues : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w)
  | .value a, .value b => .value (a - b)
  | _, _ => .poison

/-- `mul` without flags: the product modulo `2^N` of two values, and poison
when either operand is poison. -/
def mulValues : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w)
  | .value a, .value b => .value (a * b)
  | _, _ => .poison

/-- An op with the flags `f`: poison when a flag is broken on two values,
and otherwise `v`, its result without flags. `unsigned a b` and
`signed a b` say that the exact result does not fit in `N` bits, read as
unsigned and as signed. -/
def wrapValues (f : WrapFlags) (unsigned signed : BitVec w → BitVec w → Bool)
    (v : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w)) :
    PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w)
  | .value a, .value b =>
    if (f.nuw && unsigned a b) || (f.nsw && signed a b) then .poison else v (.value a) (.value b)
  | a, b => v a b

/-- `add` with the flags `f`. -/
def addWith (f : WrapFlags) : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w) :=
  wrapValues f BitVec.uaddOverflow BitVec.saddOverflow addValues

/-- `sub` with the flags `f`. -/
def subWith (f : WrapFlags) : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w) :=
  wrapValues f BitVec.usubOverflow BitVec.ssubOverflow subValues

/-- `mul` with the flags `f`. -/
def mulWith (f : WrapFlags) : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w) :=
  wrapValues f BitVec.umulOverflow BitVec.smulOverflow mulValues

/-- Without flags, `add` is the sum of the previous section. -/
theorem addWith_none (a b : PoisonOr (BitVec w)) : addWith {} a b = addValues a b := by
  cases a <;> cases b <;> rfl

/-- The flags `nuw`, `nsw`, both, or neither. -/
def WrapFlags.all : List WrapFlags := [{}, { nuw := true }, { nsw := true }, { nuw := true, nsw := true }]

-- Without flags, each op wraps, at every width.
#guard subValues (.value (-128 : BitVec 8)) (.value 1) == .value 127
#guard subValues (.value (0 : BitVec 1)) (.value 1) == .value 1
#guard mulValues (.value (-1 : BitVec 33)) (.value (-1)) == .value 1
#guard mulValues (.value (64 : BitVec 7)) (.value 2) == .value 0
-- A poison operand gives poison, with or without flags.
#guard WrapFlags.all.all fun f =>
  addWith f (.poison : PoisonOr (BitVec 8)) (.value 0) == .poison &&
  subWith f (.value (0 : BitVec 8)) .poison == .poison && mulWith (w := 8) f .poison .poison == .poison
-- `nuw` and `nsw` at `i8`: a result that fits keeps its value.
#guard addWith { nuw := true } (.value (200 : BitVec 8)) (.value 55) == .value (-1)
#guard addWith { nuw := true } (.value (200 : BitVec 8)) (.value 56) == .poison
#guard addWith { nsw := true } (.value (200 : BitVec 8)) (.value 56) == .value 0
#guard addWith { nsw := true } (.value (127 : BitVec 8)) (.value 1) == .poison
#guard addWith { nsw := true } (.value (-128 : BitVec 8)) (.value (-1)) == .poison
#guard subWith { nuw := true } (.value (1 : BitVec 8)) (.value 2) == .poison
#guard subWith { nsw := true } (.value (1 : BitVec 8)) (.value 2) == .value (-1)
#guard subWith { nsw := true } (.value (-128 : BitVec 8)) (.value 1) == .poison
#guard subWith { nuw := true } (.value (-1 : BitVec 8)) (.value (-128)) == .value 127
#guard mulWith { nuw := true } (.value (16 : BitVec 8)) (.value 16) == .poison
#guard mulWith { nsw := true } (.value (16 : BitVec 8)) (.value 8) == .poison
#guard mulWith { nsw := true } (.value (-16 : BitVec 8)) (.value 8) == .value (-128)
#guard mulWith { nuw := true } (.value (-16 : BitVec 8)) (.value 8) == .poison
-- Both flags: poison when either is broken.
#guard addWith { nuw := true, nsw := true } (.value (100 : BitVec 8)) (.value 27) == .value 127
#guard addWith { nuw := true, nsw := true } (.value (100 : BitVec 8)) (.value 28) == .poison
#guard addWith { nuw := true, nsw := true } (.value (-1 : BitVec 8)) (.value 1) == .poison
-- At `i1`, `true` is `-1` signed and `1` unsigned.
#guard addWith { nsw := true } (.value (1 : BitVec 1)) (.value 1) == .poison
#guard addWith { nuw := true } (.value (1 : BitVec 1)) (.value 1) == .poison
#guard addWith { nsw := true } (.value (1 : BitVec 1)) (.value 0) == .value 1
#guard subWith { nsw := true } (.value (0 : BitVec 1)) (.value 1) == .poison
#guard subWith { nsw := true } (.value (1 : BitVec 1)) (.value 0) == .value 1
#guard subWith { nuw := true } (.value (0 : BitVec 1)) (.value 1) == .poison
#guard mulWith { nsw := true } (.value (1 : BitVec 1)) (.value 1) == .poison
#guard mulWith { nuw := true } (.value (1 : BitVec 1)) (.value 1) == .value 1
-- At `i64`, the signed minimum and maximum.
#guard subWith { nsw := true } (.value (0 : BitVec 64)) (.value (BitVec.intMin 64)) == .poison
#guard mulWith { nsw := true } (.value (BitVec.intMin 64)) (.value (-1)) == .poison
#guard mulWith { nsw := true } (.value (BitVec.intMax 64)) (.value (-1)) ==
  .value (BitVec.intMin 64 + 1)

end Fir.Core
