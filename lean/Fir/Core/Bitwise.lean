import Fir.Core.Values

/-!
# Bitwise ops and shifts

Ticket #15 gives the bitwise ops `and`, `or` and `xor`, and the shifts
`shl`, `lshr` and `ashr`, their rules. Each takes two values of `iN` and
gives one. None of them has flags, and none is ever immediate UB. All six
propagate poison (ADR-2026-10-30-0818): a poison operand gives poison.

* `and`, `or` and `xor` work on each bit alone: bit `i` of the result is
  the and, the or or the exclusive or of bit `i` of each operand. At `i1`
  they are the boolean ops on `false` and `true`.
* `shl a, n` moves the bits of `a` up by `n` places and fills the low
  places with zeros: it gives `a · 2^n` modulo `2^N`.
* `lshr a, n` moves them down by `n` places and fills the high places with
  zeros: it gives `a`, read as unsigned, divided by `2^n` and rounded
  down.
* `ashr a, n` moves them down by `n` places and fills the high places with
  copies of the sign bit: it gives `a`, read as signed, divided by `2^n`
  and rounded towards minus infinity.

The second operand of a shift is its amount, read as unsigned. An amount
of `N` or more gives poison, and so does a poison amount, as in LLVM. An
amount whose top bit is set reads as `2^(N-1)` or more, which is never
less than `N`, so it gives poison too (`shiftValues_msb`): no amount is
read as signed, and none shifts the other way. At `i1` the amounts are
`false`, which is `0` and gives the value itself, and `true`, which is `1`,
that is `N`, and gives poison.

Poison is refined by every value, so native code may give any value for a
shift by `N` or more. A backend may compile a shift to one x86-64 shift
instruction, which masks the amount and so gives some value. A shift by
less than `N` must give exactly the value of its rule, at every width,
`i1` included.

The bitwise ops are Lean's own `&&&`, `|||` and `^^^` on `BitVec N`. The
shifts are Lean's `<<<`, `>>>` and `BitVec.sshiftRight`, and one rule,
`shiftValues`, checks the amount for all three.
-/

namespace Fir.Core

/-- `and`: the bitwise and of two values, and poison when either operand is
poison. -/
def andValues : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w)
  | .value a, .value b => .value (a &&& b)
  | _, _ => .poison

/-- `or`: the bitwise or of two values, and poison when either operand is
poison. -/
def orValues : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w)
  | .value a, .value b => .value (a ||| b)
  | _, _ => .poison

/-- `xor`: the bitwise exclusive or of two values, and poison when either
operand is poison. -/
def xorValues : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w)
  | .value a, .value b => .value (a ^^^ b)
  | _, _ => .poison

/-- A shift of a value by an amount, read as unsigned: `s a n` when the
amount `n` is less than `N`, and poison when it is `N` or more, or when
either operand is poison. -/
def shiftValues (s : BitVec w → Nat → BitVec w) :
    PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w)
  | .value a, .value n => if n.toNat < w then .value (s a n.toNat) else .poison
  | _, _ => .poison

/-- `shl`: shift left, filling with zeros. -/
def shlValues : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w) :=
  shiftValues (· <<< ·)

/-- `lshr`: logical shift right, filling with zeros. -/
def lshrValues : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w) :=
  shiftValues (· >>> ·)

/-- `ashr`: arithmetic shift right, filling with the sign bit. -/
def ashrValues : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w) :=
  shiftValues BitVec.sshiftRight

/-- An amount whose top bit is set is `N` or more, so a shift by it gives
poison, at every width. -/
theorem shiftValues_msb (s : BitVec w → Nat → BitVec w) (a : PoisonOr (BitVec w))
    {n : BitVec w} (h : n.msb = true) : shiftValues s a (.value n) = .poison := by
  cases a with
  | poison => rfl
  | value a =>
    have hn : 2 ^ (w - 1) ≤ n.toNat := of_decide_eq_true (BitVec.msb_eq_decide n ▸ h)
    have hw : w - 1 < 2 ^ (w - 1) := Nat.lt_two_pow_self
    exact ite_eq_right (by omega)

/-! # Tests

The boundary values of each width: `0`, `1`, all ones (`-1`), the signed
minimum and the signed maximum; and the shift amounts `0`, `1`, `N - 1`,
`N`, more than `N`, and amounts whose top bit is set. -/

/-- A truth table at `i1`: pairs of values, each with its result. -/
abbrev Table1 := List (BitVec 1 × BitVec 1 × BitVec 1)

-- At `i1`, the boolean truth tables, `true` being `1`.
#guard ([(0, 0, 0), (0, 1, 0), (1, 0, 0), (1, 1, 1)] : Table1).all fun (a, b, r) =>
  andValues (.value a) (.value b) == .value r
#guard ([(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 1)] : Table1).all fun (a, b, r) =>
  orValues (.value a) (.value b) == .value r
#guard ([(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)] : Table1).all fun (a, b, r) =>
  xorValues (.value a) (.value b) == .value r
-- At `i1`, a shift by `false` gives the value, and a shift by `true`,
-- which is `N`, gives poison.
#guard [0, 1].all fun (a : BitVec 1) =>
  shlValues (.value a) (.value 0) == .value a && lshrValues (.value a) (.value 0) == .value a &&
    ashrValues (.value a) (.value 0) == .value a
#guard [0, 1].all fun (a : BitVec 1) =>
  shlValues (.value a) (.value 1) == .poison && lshrValues (.value a) (.value 1) == .poison &&
    ashrValues (.value a) (.value 1) == .poison

-- At `i7`: the signed range is `-64` to `63`.
#guard andValues (.value (-1 : BitVec 7)) (.value 63) == .value 63
#guard andValues (.value (BitVec.intMin 7)) (.value (BitVec.intMax 7)) == .value 0
#guard orValues (.value (BitVec.intMin 7)) (.value (BitVec.intMax 7)) == .value (-1)
#guard orValues (.value (0 : BitVec 7)) (.value 1) == .value 1
#guard xorValues (.value (-1 : BitVec 7)) (.value (BitVec.intMin 7)) == .value (BitVec.intMax 7)
#guard xorValues (.value (-1 : BitVec 7)) (.value (-1)) == .value 0
#guard shlValues (.value (1 : BitVec 7)) (.value 6) == .value (BitVec.intMin 7)
#guard shlValues (.value (BitVec.intMax 7)) (.value 1) == .value (-2)
#guard shlValues (.value (-1 : BitVec 7)) (.value 0) == .value (-1)
#guard lshrValues (.value (BitVec.intMin 7)) (.value 6) == .value 1
#guard lshrValues (.value (-1 : BitVec 7)) (.value 1) == .value (BitVec.intMax 7)
#guard ashrValues (.value (BitVec.intMin 7)) (.value 6) == .value (-1)
#guard ashrValues (.value (BitVec.intMin 7)) (.value 1) == .value (-32)
#guard ashrValues (.value (BitVec.intMax 7)) (.value 6) == .value 0
-- At `i7`, the amounts `7`, `8`, `-64` and `-1` give poison: the last two
-- read as `64` and `127`.
#guard [7, 8, BitVec.intMin 7, -1].all fun (n : BitVec 7) =>
  shlValues (.value 1) (.value n) == .poison && lshrValues (.value (-1)) (.value n) == .poison &&
    ashrValues (.value (-1)) (.value n) == .poison

-- At `i8`: the signed range is `-128` to `127`.
#guard andValues (.value (-1 : BitVec 8)) (.value (BitVec.intMin 8)) == .value (BitVec.intMin 8)
#guard orValues (.value (BitVec.intMin 8)) (.value (BitVec.intMax 8)) == .value (-1)
#guard orValues (.value (0 : BitVec 8)) (.value 0) == .value 0
#guard xorValues (.value (BitVec.intMax 8)) (.value 1) == .value 126
#guard xorValues (.value (-1 : BitVec 8)) (.value 0) == .value (-1)
#guard shlValues (.value (1 : BitVec 8)) (.value 7) == .value (BitVec.intMin 8)
#guard shlValues (.value (-1 : BitVec 8)) (.value 7) == .value (BitVec.intMin 8)
#guard shlValues (.value (BitVec.intMax 8)) (.value 1) == .value (-2)
#guard lshrValues (.value (BitVec.intMin 8)) (.value 7) == .value 1
#guard lshrValues (.value (-1 : BitVec 8)) (.value 1) == .value (BitVec.intMax 8)
#guard lshrValues (.value (1 : BitVec 8)) (.value 1) == .value 0
#guard ashrValues (.value (BitVec.intMin 8)) (.value 7) == .value (-1)
#guard ashrValues (.value (BitVec.intMin 8)) (.value 1) == .value (-64)
#guard ashrValues (.value (BitVec.intMax 8)) (.value 7) == .value 0
#guard ashrValues (.value (-1 : BitVec 8)) (.value 1) == .value (-1)
#guard [8, 9, BitVec.intMin 8, -1].all fun (n : BitVec 8) =>
  shlValues (.value 1) (.value n) == .poison && lshrValues (.value (-1)) (.value n) == .poison &&
    ashrValues (.value 0) (.value n) == .poison

-- At `i33`: the signed range is `-2^32` to `2^32 - 1`.
#guard andValues (.value (BitVec.intMin 33)) (.value (BitVec.intMax 33)) == .value 0
#guard orValues (.value (BitVec.intMin 33)) (.value 1) == .value (BitVec.intMin 33 + 1)
#guard xorValues (.value (-1 : BitVec 33)) (.value (BitVec.intMax 33)) ==
  .value (BitVec.intMin 33)
#guard shlValues (.value (1 : BitVec 33)) (.value 32) == .value (BitVec.intMin 33)
#guard lshrValues (.value (BitVec.intMin 33)) (.value 32) == .value 1
#guard lshrValues (.value (-1 : BitVec 33)) (.value 1) == .value (BitVec.intMax 33)
#guard ashrValues (.value (BitVec.intMin 33)) (.value 32) == .value (-1)
#guard ashrValues (.value (BitVec.intMax 33)) (.value 32) == .value 0
#guard [33, 34, BitVec.intMin 33, -1].all fun (n : BitVec 33) =>
  shlValues (.value 1) (.value n) == .poison && lshrValues (.value 1) (.value n) == .poison &&
    ashrValues (.value (-1)) (.value n) == .poison

-- At `i64`.
#guard andValues (.value (BitVec.intMin 64)) (.value (-1)) == .value (BitVec.intMin 64)
#guard orValues (.value (BitVec.intMax 64)) (.value (BitVec.intMin 64)) == .value (-1)
#guard xorValues (.value (BitVec.intMax 64)) (.value (-1)) == .value (BitVec.intMin 64)
#guard shlValues (.value (1 : BitVec 64)) (.value 63) == .value (BitVec.intMin 64)
#guard shlValues (.value (BitVec.intMin 64)) (.value 1) == .value 0
#guard lshrValues (.value (-1 : BitVec 64)) (.value 63) == .value 1
#guard lshrValues (.value (BitVec.intMin 64)) (.value 0) == .value (BitVec.intMin 64)
#guard ashrValues (.value (BitVec.intMin 64)) (.value 63) == .value (-1)
#guard ashrValues (.value (BitVec.intMax 64)) (.value 62) == .value 1
#guard [64, 65, BitVec.intMin 64, -1].all fun (n : BitVec 64) =>
  shlValues (.value 1) (.value n) == .poison && lshrValues (.value 1) (.value n) == .poison &&
    ashrValues (.value 1) (.value n) == .poison

-- At `i128`, a width wider than any register.
#guard andValues (.value (BitVec.intMin 128)) (.value (BitVec.intMax 128)) == .value 0
#guard orValues (.value (BitVec.intMin 128)) (.value (BitVec.intMax 128)) == .value (-1)
#guard xorValues (.value (-1 : BitVec 128)) (.value 1) == .value (-2)
#guard shlValues (.value (1 : BitVec 128)) (.value 127) == .value (BitVec.intMin 128)
#guard lshrValues (.value (-1 : BitVec 128)) (.value 127) == .value 1
#guard ashrValues (.value (BitVec.intMin 128)) (.value 127) == .value (-1)
#guard ashrValues (.value (BitVec.intMin 128)) (.value 64) == .value (.ofInt 128 (-(2 ^ 63)))
#guard [128, 129, BitVec.intMin 128, -1].all fun (n : BitVec 128) =>
  shlValues (.value 1) (.value n) == .poison && lshrValues (.value 1) (.value n) == .poison &&
    ashrValues (.value 1) (.value n) == .poison

/-- The six rules of this section at the width `w`, for the tests. -/
def bitwiseRules (w : Nat) :
    List (PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w)) :=
  [andValues, orValues, xorValues, shlValues, lshrValues, ashrValues]

-- A poison operand gives poison, in either place, whatever the other one.
#guard (bitwiseRules 8).all fun g =>
  g .poison (.value 0) == .poison && g (.value 0) .poison == .poison &&
    g .poison .poison == .poison && g .poison (.value 8) == .poison
#guard (bitwiseRules 1).all fun g =>
  g .poison (.value 0) == .poison && g (.value 1) .poison == .poison
#guard (bitwiseRules 33).all fun g =>
  g .poison (.value 1) == .poison && g (.value (-1)) .poison == .poison
#guard (bitwiseRules 64).all fun g =>
  g .poison (.value 63) == .poison && g (.value (BitVec.intMin 64)) .poison == .poison

end Fir.Core
