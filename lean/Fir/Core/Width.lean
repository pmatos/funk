import Fir.Core.Values

/-!
# Width changes

Ticket #17 gives the width changes `zext`, `sext` and `trunc` their rules.
Each takes one value of `iM` and gives one value of `iN`:

* `zext m n` zero-extends: the result's low `M` bits are the operand's,
  and its high `N - M` bits are zero. Read as unsigned integers, the
  operand and the result are equal, so `zext` of the `i8` value `-1` to
  `i32` is `255`.
* `sext m n` sign-extends: the result's low `M` bits are the operand's,
  and each of its high `N - M` bits is a copy of the operand's top bit.
  Read as two's-complement signed integers, the operand and the result are
  equal, so `sext` of the `i8` value `-1` to `i32` is `-1`. At `i1`, `true`
  is `-1` read as signed and `1` read as unsigned, so `sext` of `true`
  gives `-1` and `zext` of `true` gives `1`.
* `trunc m n` keeps the operand's low `N` bits and drops its high `M - N`
  bits. Read as unsigned integers, the result is the operand modulo `2^N`,
  so `trunc` of the `i32` value `255` to `i8` is `-1`, and `trunc` to `i1`
  gives the operand's lowest bit.

None of them is ever UB, and none gives poison on a value. A poison
operand gives poison: the three ops propagate poison
(ADR-2026-10-30-0818).

The rules use Lean's own `BitVec.setWidth`, which pads with zeros to a
wider width and keeps the low bits at a narrower one, and
`BitVec.signExtend`, which gives the operand's signed value modulo `2^N`.
Validation admits `zext` and `sext` only when they widen, and `trunc` only
when it narrows (the core rules of validation). Lean still needs a value
at the other pairs of widths, which no valid module holds: there each rule
gives what its definition gives, so `zext` and `trunc` to the same width
give the operand. The three ops meet their obligations at every pair of
widths, valid or not, as the section on width change obligations proves.
-/

namespace Fir.Core

/-- `zext` from `iM` to `iN`: the operand's bits with zeros above them,
and poison for poison. -/
def zextValue (n : Nat) : PoisonOr (BitVec m) → PoisonOr (BitVec n)
  | .value a => .value (a.setWidth n)
  | .poison => .poison

/-- `sext` from `iM` to `iN`: the operand's bits with copies of its top
bit above them, and poison for poison. -/
def sextValue (n : Nat) : PoisonOr (BitVec m) → PoisonOr (BitVec n)
  | .value a => .value (a.signExtend n)
  | .poison => .poison

/-- `trunc` from `iM` to `iN`: the operand's low `N` bits, and poison for
poison. -/
def truncValue (n : Nat) : PoisonOr (BitVec m) → PoisonOr (BitVec n)
  | .value a => .value (a.setWidth n)
  | .poison => .poison

-- `zext` keeps the unsigned value and `sext` the signed value, so they
-- differ when the top bit is set. At `i1`, `true` is `1`.
#guard zextValue 8 (.value (1 : BitVec 1)) == .value 1
#guard sextValue 8 (.value (1 : BitVec 1)) == .value (-1)
#guard zextValue 64 (.value (0 : BitVec 1)) == .value 0 &&
  sextValue 64 (.value (0 : BitVec 1)) == .value 0
-- At `i8`: `0`, `1`, `-1`, the signed minimum and the signed maximum.
#guard zextValue 32 (.value (0 : BitVec 8)) == .value 0 &&
  sextValue 32 (.value (0 : BitVec 8)) == .value 0
#guard zextValue 32 (.value (1 : BitVec 8)) == .value 1 &&
  sextValue 32 (.value (1 : BitVec 8)) == .value 1
#guard zextValue 32 (.value (-1 : BitVec 8)) == .value 255
#guard sextValue 32 (.value (-1 : BitVec 8)) == .value (-1)
#guard zextValue 64 (.value (BitVec.intMin 8)) == .value 128
#guard sextValue 64 (.value (BitVec.intMin 8)) == .value (-128)
#guard zextValue 9 (.value (BitVec.intMax 8)) == .value 127 &&
  sextValue 9 (.value (BitVec.intMax 8)) == .value 127
-- At `i7`, `i33`, `i64` and `i128`.
#guard zextValue 8 (.value (BitVec.intMin 7)) == .value 64
#guard sextValue 8 (.value (BitVec.intMin 7)) == .value (-64)
#guard sextValue 33 (.value (BitVec.intMax 7)) == .value 63
#guard zextValue 64 (.value (-1 : BitVec 33)) == .value 8589934591
#guard sextValue 64 (.value (BitVec.intMin 33)) == .value (-4294967296)
#guard zextValue 128 (.value (BitVec.intMin 64)) == .value 9223372036854775808
#guard sextValue 128 (.value (BitVec.intMin 64)) == .value (-9223372036854775808)
#guard sextValue 128 (.value (BitVec.intMax 64)) == .value 9223372036854775807
-- `trunc` keeps the low bits: to `i1`, the lowest bit.
#guard truncValue 1 (.value (2 : BitVec 8)) == .value 0
#guard truncValue 1 (.value (-1 : BitVec 8)) == .value 1
#guard truncValue 1 (.value (BitVec.intMin 64)) == .value 0
#guard truncValue 7 (.value (BitVec.intMax 8)) == .value (-1)
#guard truncValue 7 (.value (64 : BitVec 8)) == .value (-64)
#guard truncValue 7 (.value (BitVec.intMin 33)) == .value 0
#guard truncValue 8 (.value (-1 : BitVec 33)) == .value (-1)
#guard truncValue 32 (.value (BitVec.intMax 33)) == .value (-1)
#guard truncValue 33 (.value (BitVec.intMin 64)) == .value 0
#guard truncValue 33 (.value (BitVec.intMax 64)) == .value (-1)
#guard truncValue 64 (.value (BitVec.intMin 128)) == .value 0
#guard truncValue 64 (.value (-1 : BitVec 128)) == .value (-1)
#guard truncValue 64 (.value (1 : BitVec 128)) == .value 1
-- A poison operand gives poison.
#guard zextValue 64 (.poison : PoisonOr (BitVec 8)) == .poison
#guard sextValue 8 (.poison : PoisonOr (BitVec 1)) == .poison
#guard truncValue 7 (.poison : PoisonOr (BitVec 33)) == .poison
-- At pairs that validation rejects, each rule still gives a value.
#guard zextValue 8 (.value (-1 : BitVec 8)) == .value (-1) &&
  truncValue 16 (.value (-1 : BitVec 8)) == .value 255 &&
  sextValue 4 (.value (-9 : BitVec 8)) == .value 7

end Fir.Core
