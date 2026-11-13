import Fir.Core.FloatFlags
import Fir.Core.Text

/-!
# Float comparison

This section gives `fcmp` its rule (ADR-2026-11-09-1549). It is never UB,
and its result is never a NaN.

`fcmp` takes a predicate and two values of `float<e,m>`, and gives an
`i1`: `true` when the predicate holds of them, and `false` when it does
not. It compares the numbers the operands encode, not their bits. Both
come from Lean's float model (ADR-2026-11-09-1549): `UnpackedFloat.unpack`
reads a bit pattern as a number, an infinity or a NaN, and
`UnpackedFloat.compare` says how two of them compare, or that they are
unordered because one is a NaN. So `-0` and `+0` are equal, every NaN is
unordered with every value, itself included, and the payload and sign of a
NaN do not matter. #229's first stage checked `compare` at formats other
than `f32` and `f64` (`FirTest.FloatModel`).

The `o` predicates are ordered: each is false when the operands are
unordered. The `u` predicates are unordered: each is true then. On an
ordered pair, `eq` holds when the numbers are equal, `ne` when they are
not, and `lt`, `le`, `gt` and `ge` as their names say. `ord` holds when
the pair is ordered, and `uno` when it is not. So `fcmp oeq %x, %x` is
false and `fcmp une %x, %x` true exactly when `%x` is a NaN.

`fcmp` propagates poison (ADR-2026-10-29-2006): a poison operand gives a
poison `i1`. Its fast-math flags act on its operands: under `nnan` a NaN
operand, and under `ninf` an infinite one, gives a poison `i1`. `nsz`
acts on a zero result, and `fcmp`'s result is not a float, so it changes
nothing here.

Lean's model needs at least 2 exponent bits and 1 mantissa bit. Validation
rejects every other format (ADR-2026-11-09-1549), so no valid program
compares in one. So that the rule is still total, every pair of such a
format is unordered.
-/

namespace Fir.Core

open Float.Model

/-- How two bit patterns of `float<e,m>` compare, by the numbers they
encode in Lean's float model: `none` when they are unordered. Every pair is
unordered in a format the model does not have. -/
def floatCompare (e m : Nat) (a b : BitVec (floatWidth e m)) : Option Ordering :=
  if h : 2 ≤ e ∧ 0 < m then
    let f : Format :=
      { exponentBits := e, mantissaBitsWithoutImplicit := m, he := h.1, hm := h.2 }
    (UnpackedFloat.unpack f a).compare (UnpackedFloat.unpack f b)
  else none

/-- Whether the predicate holds of two floats that compare as `c`, where
`none` is unordered. -/
def FPred.holds : FPred → Option Ordering → Bool
  | .oeq, c => c == some .eq
  | .one, c => c == some .lt || c == some .gt
  | .olt, c => c == some .lt
  | .ole, c => c == some .lt || c == some .eq
  | .ogt, c => c == some .gt
  | .oge, c => c == some .gt || c == some .eq
  | .ord, c => c.isSome
  | .ueq, c => c == none || c == some .eq
  | .une, c => c != some .eq
  | .ult, c => c == none || c == some .lt
  | .ule, c => c != some .gt
  | .ugt, c => c == none || c == some .gt
  | .uge, c => c != some .lt
  | .uno, c => c.isNone

/-- `fcmp p` under the flags `fl`: `true` when the predicate `p` holds of
two floats, `false` when it does not, and poison when either operand is
poison or breaks a flag. -/
def fcmpValues (p : FPred) (fl : FastMath) :
    PoisonOr (BitVec (floatWidth e m)) → PoisonOr (BitVec (floatWidth e m)) → PoisonOr (BitVec 1)
  | .value a, .value b =>
    if operandsBreak fl e m [a, b] then .poison else .value (.ofBool (p.holds (floatCompare e m a b)))
  | _, _ => .poison

/-!
# Tests

Bit patterns of `f32`, `f64`, `f16`, `bf16`, `f128` and `float<2,1>`: zeros
of both signs, the smallest subnormals, ones, the largest finite values,
infinities, and NaNs, quiet and signalling, with payloads and either sign.
-/

/-- The order of `a` and `b` in `f32`. -/
def cmp32 (a b : BitVec 32) : Option Ordering := floatCompare 8 23 a b

-- `+0` and `-0` are equal, and the smallest subnormal is above both.
#guard cmp32 0 0x80000000 == some .eq && cmp32 0x80000000 0 == some .eq
#guard cmp32 1 0 == some .gt && cmp32 0x80000001 0x80000000 == some .lt
-- `1.0` against `-1.0`, `+inf`, `-inf` and the largest finite value.
#guard cmp32 0x3f800000 0xbf800000 == some .gt && cmp32 0x3f800000 0x7f800000 == some .lt
#guard cmp32 0xff800000 0x3f800000 == some .lt && cmp32 0x7f7fffff 0x7f800000 == some .lt
#guard cmp32 0x7f800000 0x7f800000 == some .eq && cmp32 0xff800000 0xff800000 == some .eq
-- A NaN is unordered with everything, itself included: a quiet NaN, a
-- signalling NaN with a payload, and a NaN with its sign set.
#guard [0x7fc00000, 0x7f800001, 0xffc00000, 0xffffffff].all fun (n : BitVec 32) =>
  [0, 0x80000000, 1, 0x3f800000, 0x7f800000, 0xff800000, 0x7fc00000, n].all fun x =>
    cmp32 n x == none && cmp32 x n == none
-- Negative numbers order by magnitude, reversed.
#guard cmp32 0xc0000000 0xbf800000 == some .lt && cmp32 0x80000001 0x80000002 == some .gt

/-- What the fourteen predicates give, in the order of `FPred.all`, on a
pair that compares as `c`. -/
def fpredResults : Option Ordering → List Bool
  | some .lt => [false, true, true, true, false, false, true, false, true, true, true, false, false, false]
  | some .eq => [true, false, false, true, false, true, true, true, false, false, true, false, true, false]
  | some .gt => [false, true, false, false, true, true, true, false, true, false, false, true, true, false]
  | none => [false, false, false, false, false, false, false, true, true, true, true, true, true, true]

#guard [some .lt, some .eq, some .gt, none].all fun c => FPred.all.map (·.holds c) == fpredResults c

/-- `fcmp` gives, with each predicate, what `fpredResults` says of how `a`
and `b` compare. -/
def fcmpsAs (e m : Nat) (a b : BitVec (floatWidth e m)) (c : Option Ordering) : Bool :=
  FPred.all.map (fcmpValues · {} (.value a) (.value b)) == (fpredResults c).map fun r => .value (.ofBool r)

-- At `f32`: `1.0 < 2.0`, `-0 = +0`, and a NaN against `1.0`.
#guard fcmpsAs 8 23 0x3f800000 0x40000000 (some .lt)
#guard fcmpsAs 8 23 0x80000000 0 (some .eq)
#guard fcmpsAs 8 23 0x7fc00000 0x3f800000 none
-- At `f64`: the largest finite value against `+inf`, the smallest
-- subnormals of either sign, and a signalling NaN with its sign set.
#guard fcmpsAs 11 52 0x7fefffffffffffff 0x7ff0000000000000 (some .lt)
#guard fcmpsAs 11 52 1 0x8000000000000001 (some .gt)
#guard fcmpsAs 11 52 0xfff0000000000001 0xfff0000000000001 none
-- At `f16`, `bf16` and `f128`: `-inf` below the largest negative number,
-- `1.0` equal to itself, and a NaN.
#guard fcmpsAs 5 10 0xfc00 0xfbff (some .lt)
#guard fcmpsAs 8 7 0x3f80 0x3f80 (some .eq)
#guard fcmpsAs 15 112 0x7fff8000000000000000000000000000 0 none
-- At `float<2,1>`, whose 16 patterns are listed in `FirTest.FloatModel`:
-- `0.5 < 3`, `-0 = +0`, and the NaN 7 against `+inf`, 6.
#guard fcmpsAs 2 1 1 5 (some .lt) && fcmpsAs 2 1 8 0 (some .eq) && fcmpsAs 2 1 7 6 none
-- A format the model does not have compares nothing: every pair is
-- unordered.
#guard floatCompare 1 1 0 0 == none && floatCompare 2 0 1 1 == none

-- A poison operand gives poison, with every predicate, in either place.
#guard FPred.all.all fun p =>
  fcmpValues (e := 8) (m := 23) p {} .poison (.value 0) == .poison &&
    fcmpValues (e := 8) (m := 23) p {} (.value 0x7fc00000) .poison == .poison &&
    fcmpValues (e := 11) (m := 52) p {} .poison .poison == .poison

-- Under `nnan`, a NaN operand gives poison with every predicate, `uno`
-- included; under `ninf`, an infinite one does. `nsz` changes nothing.
#guard FPred.all.all fun p =>
  fcmpValues (e := 8) (m := 23) p { nnan := true } (.value 0x7fc00000) (.value 0) == .poison &&
    fcmpValues (e := 8) (m := 23) p { ninf := true } (.value 0) (.value 0xff800000) == .poison &&
    fcmpValues (e := 8) (m := 23) p { nnan := true } (.value 0) (.value 0xff800000) ==
      fcmpValues (e := 8) (m := 23) p {} (.value 0) (.value 0xff800000) &&
    fcmpValues (e := 8) (m := 23) p { nsz := true } (.value 0x80000000) (.value 0) ==
      fcmpValues (e := 8) (m := 23) p {} (.value 0x80000000) (.value 0)

end Fir.Core
