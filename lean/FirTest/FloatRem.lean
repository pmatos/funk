import FirTest.FloatModel
import Fir.Core.FloatRem

/-!
Known answers for fir's remainder (#310), `Fir.Core.remainder`, which
`frem` and `fmod` compute on Lean's float model: on the hard inputs at
`f16`, `bf16`, `f64` and `f128`, and on every input at `float<2,1>`.
Each expected bit pattern was computed apart from Lean's code, with exact
rational arithmetic, by `scripts/harness/float_ref.py`, and
`scripts/harness/float_rem_cases.py` writes this module. The symbols:
`s` is the smallest subnormal, `S` the largest subnormal, `n` the
smallest normal number, `M` the largest finite number and `P` the
largest power of two. A NaN result is the model's one canonical NaN.
-/

namespace FirTest.FloatModel

open Float.Model

/-- `a frem b` in format `f`: IEEE 754's remainder. -/
def frem (f : Format) (a b : Nat) : Nat := pk f (Fir.Core.remainder true f (un f a) (un f b))

/-- `a fmod b` in format `f`: C's `fmod`. -/
def fmod (f : Format) (a b : Nat) : Nat := pk f (Fir.Core.remainder false f (un f a) (un f b))

/-! # At `f16` -/

-- 5.5 frem 2 = -0.5: the quotient 2.75 goes to 3
#guard frem f16 0x4580 0x4000 == 0xB800
-- -5.5 frem 2 = 0.5
#guard frem f16 0xC580 0x4000 == 0x3800
-- 5.5 frem -2 = -0.5: y's sign does not matter
#guard frem f16 0x4580 0xC000 == 0xB800
-- 3 frem 2 = -1: the tie 1.5 goes to the even 2
#guard frem f16 0x4200 0x4000 == 0xBC00
-- 5 frem 2 = 1: the tie 2.5 goes to the even 2
#guard frem f16 0x4500 0x4000 == 0x3C00
-- 1 frem 3 = 1: the quotient goes to 0
#guard frem f16 0x3C00 0x4200 == 0x3C00
-- 2 frem 3 = -1: the quotient goes to 1
#guard frem f16 0x4000 0x4200 == 0xBC00
-- 4 frem 2 = +0
#guard frem f16 0x4400 0x4000 == 0x0000
-- -4 frem 2 = -0: a zero has x's sign
#guard frem f16 0xC400 0x4000 == 0x8000
-- M frem s = +0: M is a multiple of s
#guard frem f16 0x7BFF 0x0001 == 0x0000
-- P frem 3s: x and y far apart
#guard frem f16 0x7800 0x0003 == 0x8001
-- S frem 2s = -s: a tie to the even quotient
#guard frem f16 0x03FF 0x0002 == 0x8001
-- n frem 3s, subnormal
#guard frem f16 0x0400 0x0003 == 0x0001
-- 1 frem inf = 1
#guard frem f16 0x3C00 0x7C00 == 0x3C00
-- -0 frem inf = -0
#guard frem f16 0x8000 0x7C00 == 0x8000
-- -0 frem 1 = -0
#guard frem f16 0x8000 0x3C00 == 0x8000
-- 1 frem +0 is NaN
#guard frem f16 0x3C00 0x0000 == 0x7E00
-- inf frem 1 is NaN
#guard frem f16 0x7C00 0x3C00 == 0x7E00
-- inf frem inf is NaN
#guard frem f16 0x7C00 0x7C00 == 0x7E00
-- +0 frem +0 is NaN
#guard frem f16 0x0000 0x0000 == 0x7E00
-- a NaN operand gives the canonical NaN
#guard frem f16 0xFFFF 0x3C00 == 0x7E00
-- a signalling NaN gives the canonical NaN
#guard frem f16 0x3C00 0x7C01 == 0x7E00
-- 5.5 fmod 2 = 1.5: the quotient 2.75 goes to 2
#guard fmod f16 0x4580 0x4000 == 0x3E00
-- -5.5 fmod 2 = -1.5
#guard fmod f16 0xC580 0x4000 == 0xBE00
-- 5.5 fmod -2 = 1.5: y's sign does not matter
#guard fmod f16 0x4580 0xC000 == 0x3E00
-- 3 fmod 2 = 1
#guard fmod f16 0x4200 0x4000 == 0x3C00
-- -4 fmod 2 = -0: a zero has x's sign
#guard fmod f16 0xC400 0x4000 == 0x8000
-- 1 fmod 3 = 1
#guard fmod f16 0x3C00 0x4200 == 0x3C00
-- -M fmod s = -0
#guard fmod f16 0xFBFF 0x0001 == 0x8000
-- P fmod 3s: x and y far apart
#guard fmod f16 0x7800 0x0003 == 0x0002
-- M fmod (M - ulp M) = ulp M
#guard fmod f16 0x7BFF 0x7BFE == 0x5000
-- n fmod 3s, subnormal
#guard fmod f16 0x0400 0x0003 == 0x0001
-- M fmod -inf = M
#guard fmod f16 0x7BFF 0xFC00 == 0x7BFF
-- +0 fmod 1 = +0
#guard fmod f16 0x0000 0x3C00 == 0x0000
-- 1 fmod -0 is NaN
#guard fmod f16 0x3C00 0x8000 == 0x7E00
-- -inf fmod 1 is NaN
#guard fmod f16 0xFC00 0x3C00 == 0x7E00
-- a NaN operand gives the canonical NaN
#guard fmod f16 0xFFFF 0x7C00 == 0x7E00

/-! # At `bf16` -/

-- 5.5 frem 2 = -0.5: the quotient 2.75 goes to 3
#guard frem bf16 0x40B0 0x4000 == 0xBF00
-- -5.5 frem 2 = 0.5
#guard frem bf16 0xC0B0 0x4000 == 0x3F00
-- 5.5 frem -2 = -0.5: y's sign does not matter
#guard frem bf16 0x40B0 0xC000 == 0xBF00
-- 3 frem 2 = -1: the tie 1.5 goes to the even 2
#guard frem bf16 0x4040 0x4000 == 0xBF80
-- 5 frem 2 = 1: the tie 2.5 goes to the even 2
#guard frem bf16 0x40A0 0x4000 == 0x3F80
-- 1 frem 3 = 1: the quotient goes to 0
#guard frem bf16 0x3F80 0x4040 == 0x3F80
-- 2 frem 3 = -1: the quotient goes to 1
#guard frem bf16 0x4000 0x4040 == 0xBF80
-- 4 frem 2 = +0
#guard frem bf16 0x4080 0x4000 == 0x0000
-- -4 frem 2 = -0: a zero has x's sign
#guard frem bf16 0xC080 0x4000 == 0x8000
-- M frem s = +0: M is a multiple of s
#guard frem bf16 0x7F7F 0x0001 == 0x0000
-- P frem 3s: x and y far apart
#guard frem bf16 0x7F00 0x0003 == 0x0001
-- S frem 2s = -s: a tie to the even quotient
#guard frem bf16 0x007F 0x0002 == 0x8001
-- n frem 3s, subnormal
#guard frem bf16 0x0080 0x0003 == 0x8001
-- 1 frem inf = 1
#guard frem bf16 0x3F80 0x7F80 == 0x3F80
-- -0 frem inf = -0
#guard frem bf16 0x8000 0x7F80 == 0x8000
-- -0 frem 1 = -0
#guard frem bf16 0x8000 0x3F80 == 0x8000
-- 1 frem +0 is NaN
#guard frem bf16 0x3F80 0x0000 == 0x7FC0
-- inf frem 1 is NaN
#guard frem bf16 0x7F80 0x3F80 == 0x7FC0
-- inf frem inf is NaN
#guard frem bf16 0x7F80 0x7F80 == 0x7FC0
-- +0 frem +0 is NaN
#guard frem bf16 0x0000 0x0000 == 0x7FC0
-- a NaN operand gives the canonical NaN
#guard frem bf16 0xFFFF 0x3F80 == 0x7FC0
-- a signalling NaN gives the canonical NaN
#guard frem bf16 0x3F80 0x7F81 == 0x7FC0
-- 5.5 fmod 2 = 1.5: the quotient 2.75 goes to 2
#guard fmod bf16 0x40B0 0x4000 == 0x3FC0
-- -5.5 fmod 2 = -1.5
#guard fmod bf16 0xC0B0 0x4000 == 0xBFC0
-- 5.5 fmod -2 = 1.5: y's sign does not matter
#guard fmod bf16 0x40B0 0xC000 == 0x3FC0
-- 3 fmod 2 = 1
#guard fmod bf16 0x4040 0x4000 == 0x3F80
-- -4 fmod 2 = -0: a zero has x's sign
#guard fmod bf16 0xC080 0x4000 == 0x8000
-- 1 fmod 3 = 1
#guard fmod bf16 0x3F80 0x4040 == 0x3F80
-- -M fmod s = -0
#guard fmod bf16 0xFF7F 0x0001 == 0x8000
-- P fmod 3s: x and y far apart
#guard fmod bf16 0x7F00 0x0003 == 0x0001
-- M fmod (M - ulp M) = ulp M
#guard fmod bf16 0x7F7F 0x7F7E == 0x7B80
-- n fmod 3s, subnormal
#guard fmod bf16 0x0080 0x0003 == 0x0002
-- M fmod -inf = M
#guard fmod bf16 0x7F7F 0xFF80 == 0x7F7F
-- +0 fmod 1 = +0
#guard fmod bf16 0x0000 0x3F80 == 0x0000
-- 1 fmod -0 is NaN
#guard fmod bf16 0x3F80 0x8000 == 0x7FC0
-- -inf fmod 1 is NaN
#guard fmod bf16 0xFF80 0x3F80 == 0x7FC0
-- a NaN operand gives the canonical NaN
#guard fmod bf16 0xFFFF 0x7F80 == 0x7FC0

/-! # At `f64` -/

-- 5.5 frem 2 = -0.5: the quotient 2.75 goes to 3
#guard frem .binary64 0x4016000000000000 0x4000000000000000 == 0xBFE0000000000000
-- -5.5 frem 2 = 0.5
#guard frem .binary64 0xC016000000000000 0x4000000000000000 == 0x3FE0000000000000
-- 5.5 frem -2 = -0.5: y's sign does not matter
#guard frem .binary64 0x4016000000000000 0xC000000000000000 == 0xBFE0000000000000
-- 3 frem 2 = -1: the tie 1.5 goes to the even 2
#guard frem .binary64 0x4008000000000000 0x4000000000000000 == 0xBFF0000000000000
-- 5 frem 2 = 1: the tie 2.5 goes to the even 2
#guard frem .binary64 0x4014000000000000 0x4000000000000000 == 0x3FF0000000000000
-- 1 frem 3 = 1: the quotient goes to 0
#guard frem .binary64 0x3FF0000000000000 0x4008000000000000 == 0x3FF0000000000000
-- 2 frem 3 = -1: the quotient goes to 1
#guard frem .binary64 0x4000000000000000 0x4008000000000000 == 0xBFF0000000000000
-- 4 frem 2 = +0
#guard frem .binary64 0x4010000000000000 0x4000000000000000 == 0x0000000000000000
-- -4 frem 2 = -0: a zero has x's sign
#guard frem .binary64 0xC010000000000000 0x4000000000000000 == 0x8000000000000000
-- M frem s = +0: M is a multiple of s
#guard frem .binary64 0x7FEFFFFFFFFFFFFF 0x0000000000000001 == 0x0000000000000000
-- P frem 3s: x and y far apart
#guard frem .binary64 0x7FE0000000000000 0x0000000000000003 == 0x8000000000000001
-- S frem 2s = -s: a tie to the even quotient
#guard frem .binary64 0x000FFFFFFFFFFFFF 0x0000000000000002 == 0x8000000000000001
-- n frem 3s, subnormal
#guard frem .binary64 0x0010000000000000 0x0000000000000003 == 0x0000000000000001
-- 1 frem inf = 1
#guard frem .binary64 0x3FF0000000000000 0x7FF0000000000000 == 0x3FF0000000000000
-- -0 frem inf = -0
#guard frem .binary64 0x8000000000000000 0x7FF0000000000000 == 0x8000000000000000
-- -0 frem 1 = -0
#guard frem .binary64 0x8000000000000000 0x3FF0000000000000 == 0x8000000000000000
-- 1 frem +0 is NaN
#guard frem .binary64 0x3FF0000000000000 0x0000000000000000 == 0x7FF8000000000000
-- inf frem 1 is NaN
#guard frem .binary64 0x7FF0000000000000 0x3FF0000000000000 == 0x7FF8000000000000
-- inf frem inf is NaN
#guard frem .binary64 0x7FF0000000000000 0x7FF0000000000000 == 0x7FF8000000000000
-- +0 frem +0 is NaN
#guard frem .binary64 0x0000000000000000 0x0000000000000000 == 0x7FF8000000000000
-- a NaN operand gives the canonical NaN
#guard frem .binary64 0xFFFFFFFFFFFFFFFF 0x3FF0000000000000 == 0x7FF8000000000000
-- a signalling NaN gives the canonical NaN
#guard frem .binary64 0x3FF0000000000000 0x7FF0000000000001 == 0x7FF8000000000000
-- 5.5 fmod 2 = 1.5: the quotient 2.75 goes to 2
#guard fmod .binary64 0x4016000000000000 0x4000000000000000 == 0x3FF8000000000000
-- -5.5 fmod 2 = -1.5
#guard fmod .binary64 0xC016000000000000 0x4000000000000000 == 0xBFF8000000000000
-- 5.5 fmod -2 = 1.5: y's sign does not matter
#guard fmod .binary64 0x4016000000000000 0xC000000000000000 == 0x3FF8000000000000
-- 3 fmod 2 = 1
#guard fmod .binary64 0x4008000000000000 0x4000000000000000 == 0x3FF0000000000000
-- -4 fmod 2 = -0: a zero has x's sign
#guard fmod .binary64 0xC010000000000000 0x4000000000000000 == 0x8000000000000000
-- 1 fmod 3 = 1
#guard fmod .binary64 0x3FF0000000000000 0x4008000000000000 == 0x3FF0000000000000
-- -M fmod s = -0
#guard fmod .binary64 0xFFEFFFFFFFFFFFFF 0x0000000000000001 == 0x8000000000000000
-- P fmod 3s: x and y far apart
#guard fmod .binary64 0x7FE0000000000000 0x0000000000000003 == 0x0000000000000002
-- M fmod (M - ulp M) = ulp M
#guard fmod .binary64 0x7FEFFFFFFFFFFFFF 0x7FEFFFFFFFFFFFFE == 0x7CA0000000000000
-- n fmod 3s, subnormal
#guard fmod .binary64 0x0010000000000000 0x0000000000000003 == 0x0000000000000001
-- M fmod -inf = M
#guard fmod .binary64 0x7FEFFFFFFFFFFFFF 0xFFF0000000000000 == 0x7FEFFFFFFFFFFFFF
-- +0 fmod 1 = +0
#guard fmod .binary64 0x0000000000000000 0x3FF0000000000000 == 0x0000000000000000
-- 1 fmod -0 is NaN
#guard fmod .binary64 0x3FF0000000000000 0x8000000000000000 == 0x7FF8000000000000
-- -inf fmod 1 is NaN
#guard fmod .binary64 0xFFF0000000000000 0x3FF0000000000000 == 0x7FF8000000000000
-- a NaN operand gives the canonical NaN
#guard fmod .binary64 0xFFFFFFFFFFFFFFFF 0x7FF0000000000000 == 0x7FF8000000000000

/-! # At `f128` -/

-- 5.5 frem 2 = -0.5: the quotient 2.75 goes to 3
#guard frem f128 0x40016000000000000000000000000000 0x40000000000000000000000000000000 == 0xBFFE0000000000000000000000000000
-- -5.5 frem 2 = 0.5
#guard frem f128 0xC0016000000000000000000000000000 0x40000000000000000000000000000000 == 0x3FFE0000000000000000000000000000
-- 5.5 frem -2 = -0.5: y's sign does not matter
#guard frem f128 0x40016000000000000000000000000000 0xC0000000000000000000000000000000 == 0xBFFE0000000000000000000000000000
-- 3 frem 2 = -1: the tie 1.5 goes to the even 2
#guard frem f128 0x40008000000000000000000000000000 0x40000000000000000000000000000000 == 0xBFFF0000000000000000000000000000
-- 5 frem 2 = 1: the tie 2.5 goes to the even 2
#guard frem f128 0x40014000000000000000000000000000 0x40000000000000000000000000000000 == 0x3FFF0000000000000000000000000000
-- 1 frem 3 = 1: the quotient goes to 0
#guard frem f128 0x3FFF0000000000000000000000000000 0x40008000000000000000000000000000 == 0x3FFF0000000000000000000000000000
-- 2 frem 3 = -1: the quotient goes to 1
#guard frem f128 0x40000000000000000000000000000000 0x40008000000000000000000000000000 == 0xBFFF0000000000000000000000000000
-- 4 frem 2 = +0
#guard frem f128 0x40010000000000000000000000000000 0x40000000000000000000000000000000 == 0x00000000000000000000000000000000
-- -4 frem 2 = -0: a zero has x's sign
#guard frem f128 0xC0010000000000000000000000000000 0x40000000000000000000000000000000 == 0x80000000000000000000000000000000
-- M frem s = +0: M is a multiple of s
#guard frem f128 0x7FFEFFFFFFFFFFFFFFFFFFFFFFFFFFFF 0x00000000000000000000000000000001 == 0x00000000000000000000000000000000
-- P frem 3s: x and y far apart
#guard frem f128 0x7FFE0000000000000000000000000000 0x00000000000000000000000000000003 == 0x80000000000000000000000000000001
-- S frem 2s = -s: a tie to the even quotient
#guard frem f128 0x0000FFFFFFFFFFFFFFFFFFFFFFFFFFFF 0x00000000000000000000000000000002 == 0x80000000000000000000000000000001
-- n frem 3s, subnormal
#guard frem f128 0x00010000000000000000000000000000 0x00000000000000000000000000000003 == 0x00000000000000000000000000000001
-- 1 frem inf = 1
#guard frem f128 0x3FFF0000000000000000000000000000 0x7FFF0000000000000000000000000000 == 0x3FFF0000000000000000000000000000
-- -0 frem inf = -0
#guard frem f128 0x80000000000000000000000000000000 0x7FFF0000000000000000000000000000 == 0x80000000000000000000000000000000
-- -0 frem 1 = -0
#guard frem f128 0x80000000000000000000000000000000 0x3FFF0000000000000000000000000000 == 0x80000000000000000000000000000000
-- 1 frem +0 is NaN
#guard frem f128 0x3FFF0000000000000000000000000000 0x00000000000000000000000000000000 == 0x7FFF8000000000000000000000000000
-- inf frem 1 is NaN
#guard frem f128 0x7FFF0000000000000000000000000000 0x3FFF0000000000000000000000000000 == 0x7FFF8000000000000000000000000000
-- inf frem inf is NaN
#guard frem f128 0x7FFF0000000000000000000000000000 0x7FFF0000000000000000000000000000 == 0x7FFF8000000000000000000000000000
-- +0 frem +0 is NaN
#guard frem f128 0x00000000000000000000000000000000 0x00000000000000000000000000000000 == 0x7FFF8000000000000000000000000000
-- a NaN operand gives the canonical NaN
#guard frem f128 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 0x3FFF0000000000000000000000000000 == 0x7FFF8000000000000000000000000000
-- a signalling NaN gives the canonical NaN
#guard frem f128 0x3FFF0000000000000000000000000000 0x7FFF0000000000000000000000000001 == 0x7FFF8000000000000000000000000000
-- 5.5 fmod 2 = 1.5: the quotient 2.75 goes to 2
#guard fmod f128 0x40016000000000000000000000000000 0x40000000000000000000000000000000 == 0x3FFF8000000000000000000000000000
-- -5.5 fmod 2 = -1.5
#guard fmod f128 0xC0016000000000000000000000000000 0x40000000000000000000000000000000 == 0xBFFF8000000000000000000000000000
-- 5.5 fmod -2 = 1.5: y's sign does not matter
#guard fmod f128 0x40016000000000000000000000000000 0xC0000000000000000000000000000000 == 0x3FFF8000000000000000000000000000
-- 3 fmod 2 = 1
#guard fmod f128 0x40008000000000000000000000000000 0x40000000000000000000000000000000 == 0x3FFF0000000000000000000000000000
-- -4 fmod 2 = -0: a zero has x's sign
#guard fmod f128 0xC0010000000000000000000000000000 0x40000000000000000000000000000000 == 0x80000000000000000000000000000000
-- 1 fmod 3 = 1
#guard fmod f128 0x3FFF0000000000000000000000000000 0x40008000000000000000000000000000 == 0x3FFF0000000000000000000000000000
-- -M fmod s = -0
#guard fmod f128 0xFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFF 0x00000000000000000000000000000001 == 0x80000000000000000000000000000000
-- P fmod 3s: x and y far apart
#guard fmod f128 0x7FFE0000000000000000000000000000 0x00000000000000000000000000000003 == 0x00000000000000000000000000000002
-- M fmod (M - ulp M) = ulp M
#guard fmod f128 0x7FFEFFFFFFFFFFFFFFFFFFFFFFFFFFFF 0x7FFEFFFFFFFFFFFFFFFFFFFFFFFFFFFE == 0x7F8E0000000000000000000000000000
-- n fmod 3s, subnormal
#guard fmod f128 0x00010000000000000000000000000000 0x00000000000000000000000000000003 == 0x00000000000000000000000000000001
-- M fmod -inf = M
#guard fmod f128 0x7FFEFFFFFFFFFFFFFFFFFFFFFFFFFFFF 0xFFFF0000000000000000000000000000 == 0x7FFEFFFFFFFFFFFFFFFFFFFFFFFFFFFF
-- +0 fmod 1 = +0
#guard fmod f128 0x00000000000000000000000000000000 0x3FFF0000000000000000000000000000 == 0x00000000000000000000000000000000
-- 1 fmod -0 is NaN
#guard fmod f128 0x3FFF0000000000000000000000000000 0x80000000000000000000000000000000 == 0x7FFF8000000000000000000000000000
-- -inf fmod 1 is NaN
#guard fmod f128 0xFFFF0000000000000000000000000000 0x3FFF0000000000000000000000000000 == 0x7FFF8000000000000000000000000000
-- a NaN operand gives the canonical NaN
#guard fmod f128 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 0x7FFF0000000000000000000000000000 == 0x7FFF8000000000000000000000000000

/-! # Every input at `float<2,1>` -/

#guard table (frem tiny) == [
  [7, 0, 0, 0, 0, 0, 0, 7, 7, 0, 0, 0, 0, 0, 0, 7],
  [7, 0, 1, 1, 1, 1, 1, 7, 7, 0, 1, 1, 1, 1, 1, 7],
  [7, 0, 0, 9, 2, 2, 2, 7, 7, 0, 0, 9, 2, 2, 2, 7],
  [7, 0, 9, 0, 9, 3, 3, 7, 7, 0, 9, 0, 9, 3, 3, 7],
  [7, 0, 0, 1, 0, 10, 4, 7, 7, 0, 0, 1, 0, 10, 4, 7],
  [7, 0, 0, 0, 10, 0, 5, 7, 7, 0, 0, 0, 10, 0, 5, 7],
  [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7],
  [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7],
  [7, 8, 8, 8, 8, 8, 8, 7, 7, 8, 8, 8, 8, 8, 8, 7],
  [7, 8, 9, 9, 9, 9, 9, 7, 7, 8, 9, 9, 9, 9, 9, 7],
  [7, 8, 8, 1, 10, 10, 10, 7, 7, 8, 8, 1, 10, 10, 10, 7],
  [7, 8, 1, 8, 1, 11, 11, 7, 7, 8, 1, 8, 1, 11, 11, 7],
  [7, 8, 8, 9, 8, 2, 12, 7, 7, 8, 8, 9, 8, 2, 12, 7],
  [7, 8, 8, 8, 2, 8, 13, 7, 7, 8, 8, 8, 2, 8, 13, 7],
  [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7],
  [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]]
#guard table (fmod tiny) == [
  [7, 0, 0, 0, 0, 0, 0, 7, 7, 0, 0, 0, 0, 0, 0, 7],
  [7, 0, 1, 1, 1, 1, 1, 7, 7, 0, 1, 1, 1, 1, 1, 7],
  [7, 0, 0, 2, 2, 2, 2, 7, 7, 0, 0, 2, 2, 2, 2, 7],
  [7, 0, 1, 0, 3, 3, 3, 7, 7, 0, 1, 0, 3, 3, 3, 7],
  [7, 0, 0, 1, 0, 4, 4, 7, 7, 0, 0, 1, 0, 4, 4, 7],
  [7, 0, 0, 0, 2, 0, 5, 7, 7, 0, 0, 0, 2, 0, 5, 7],
  [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7],
  [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7],
  [7, 8, 8, 8, 8, 8, 8, 7, 7, 8, 8, 8, 8, 8, 8, 7],
  [7, 8, 9, 9, 9, 9, 9, 7, 7, 8, 9, 9, 9, 9, 9, 7],
  [7, 8, 8, 10, 10, 10, 10, 7, 7, 8, 8, 10, 10, 10, 10, 7],
  [7, 8, 9, 8, 11, 11, 11, 7, 7, 8, 9, 8, 11, 11, 11, 7],
  [7, 8, 8, 9, 8, 12, 12, 7, 7, 8, 8, 9, 8, 12, 12, 7],
  [7, 8, 8, 8, 10, 8, 13, 7, 7, 8, 8, 8, 10, 8, 13, 7],
  [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7],
  [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]]

end FirTest.FloatModel
