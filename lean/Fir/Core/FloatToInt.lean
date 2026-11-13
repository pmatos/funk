import Fir.Core.Values

/-!
# Conversions from floats to integers

This section gives `fptosi` and `fptoui` their rule (ADR-2026-11-09-1549).
Each takes a value of `float<e,m>` and gives a value of `iN`, for any
format and any `N`. The human ruled on 2026-11-12, on #354, that both
truncate toward zero: the fraction is cut off, so `2.7` gives `2` and
`-2.7` gives `-2`. This is IEEE 754's `convertToIntegerTowardZero`
(§5.8), C's `(int)x`, Rust's `as` and LLVM's `fptosi` and `fptoui`.
Truncation is what the ops mean, so neither carries a rounding attribute.

Lean's float model reads the operand: `UnpackedFloat.unpack` gives a
signed zero, a finite number, a signed infinity or a NaN, and the model's
`UnpackedFloat.roundToInt` cuts a finite number's fraction off, toward
zero. Then

* `fptosi` gives the integer when `iN` holds it read as signed, from
  `-2^(N-1)` to `2^(N-1) - 1`, as its bits in two's complement;
* `fptoui` gives it when `iN` holds it read as unsigned, from `0` to
  `2^N - 1`;
* a zero of either sign gives `0`, and so does a number whose integer part
  is zero: `fptoui` of `-0.5` is `0`, since `-0.5` truncates to `0`;
* an integer that `iN` does not hold, an infinity and a NaN give poison
  (#241): `fptosi` of the `f32` value `2^31` to `i32` is poison, and so is
  `fptoui` of `-1.0`.

The rule is fir's own in two more places: a poison operand gives poison
(ADR-2026-10-29-2006), and a format that the model does not have, which
validation rejects, gives poison too, so that the rule is total. The rule
chooses nothing, and neither op is ever UB. An op may produce poison on a
defined operand, so each declares `mayPoison`, as the shifts do.
-/

namespace Fir.Core

open Float.Model

/-- The integer of the model's number `u`, its fraction cut off toward
zero, or none for an infinity or a NaN. -/
def truncInt : UnpackedFloat → Option Int
  | .zero _ => some 0
  | .finite s mt ex _ => some (UnpackedFloat.roundToInt s mt ex)
  | .infinity _ | .notANumber => none

/-- Whether `iN` holds the integer `k`: from `-2^(N-1)` to `2^(N-1) - 1`
when `signed`, written without `N - 1` so that it holds at `N = 0` too,
and from `0` to `2^N - 1` otherwise. -/
def intFits (signed : Bool) (n : Nat) (k : Int) : Bool :=
  if signed then -(2 ^ n : Int) ≤ 2 * k ∧ 2 * k < 2 ^ n else 0 ≤ k ∧ k < 2 ^ n

/-- The rule of `fptosi`, with `signed`, and of `fptoui`, from
`float<e,m>` to `iN`: the operand's number truncated toward zero, when
`iN` holds it, and poison otherwise, on an infinity, a NaN and poison. -/
def floatToInt (e m : Nat) (signed : Bool) :
    PoisonOr (BitVec (floatWidth e m)) → PoisonOr (BitVec n)
  | .value a =>
    if h : 2 ≤ e ∧ 0 < m then
      match truncInt (UnpackedFloat.unpack
          { exponentBits := e, mantissaBitsWithoutImplicit := m, he := h.1, hm := h.2 } a) with
      | some k => if intFits signed n k then .value (BitVec.ofInt n k) else .poison
      | none => .poison
    else .poison
  | .poison => .poison

/-! # Tests

`FirTest.FloatToInt` runs both ops on the boundary values of each format
and width. These check the rule on a few of them.
-/

-- `2.7` truncates to `2`, `-2.7` to `-2`, and `-0.5` to `0` for both ops.
#guard floatToInt (n := 32) 8 23 true (.value 0x402ccccd) == .value 2
#guard floatToInt (n := 32) 8 23 true (.value 0xc02ccccd) == .value (-2)
#guard floatToInt (n := 8) 8 23 false (.value 0xbf000000) == .value 0
#guard floatToInt (n := 8) 8 23 true (.value 0xbf000000) == .value 0
-- `-1.0` is poison for `fptoui`, and `-1` for `fptosi`.
#guard floatToInt (n := 8) 8 23 false (.value 0xbf800000) == .poison
#guard floatToInt (n := 8) 8 23 true (.value 0xbf800000) == .value 0xff
-- At `i32`, `2^31 - 128`, the largest `f32` below `2^31`, is in range and
-- `2^31` is not, for `fptosi`; `-2^31` is, and `fptoui` holds `2^31`.
#guard floatToInt (n := 32) 8 23 true (.value 0x4effffff) == .value 2147483520
#guard floatToInt (n := 32) 8 23 true (.value 0x4f000000) == .poison
#guard floatToInt (n := 32) 8 23 true (.value 0xcf000000) == .value 0x80000000
#guard floatToInt (n := 32) 8 23 false (.value 0x4f000000) == .value 0x80000000
-- `i1` holds `-1` and `0` signed, and `0` and `1` unsigned.
#guard floatToInt (n := 1) 8 23 true (.value 0xbf800000) == .value 1
#guard floatToInt (n := 1) 8 23 true (.value 0x3f800000) == .poison
#guard floatToInt (n := 1) 8 23 false (.value 0x3ff33333) == .value 1
#guard floatToInt (n := 1) 8 23 false (.value 0x40000000) == .poison
-- Infinities and NaNs are poison; the smallest subnormal is `0`.
#guard floatToInt (n := 64) 8 23 true (.value 0x7f800000) == .poison
#guard floatToInt (n := 64) 8 23 false (.value 0x7fc00000) == .poison
#guard floatToInt (n := 64) 8 23 true (.value 0x00000001) == .value 0
#guard floatToInt (n := 64) 8 23 false (.value 0x80000001) == .value 0
-- A format that validation rejects gives poison, and so does poison.
#guard floatToInt (n := 8) 1 1 true (.value 0) == .poison
#guard floatToInt (n := 8) 8 23 false .poison == .poison

end Fir.Core
