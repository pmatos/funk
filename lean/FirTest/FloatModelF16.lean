import FirTest.FloatModel

/-!
Known answers for Lean's float model at `f16`, `float<5,10>`, on the hard
inputs: ties, subnormals, `-0`, overflow to infinity and NaN operands
(#229). Each expected bit pattern was computed apart from Lean's code,
with exact rational arithmetic, and each case's comment says what the
result is. The symbols: `u` is an ulp of 1, `2^-10`, and `h` is `u/2`;
`s` is the smallest subnormal, `S` the largest subnormal, `n` the
smallest normal number, `M` the largest finite number, and `H` half an
ulp of `M`. A NaN result is the model's one canonical NaN. `nanp` is a
NaN with every bit set, and a signalling NaN has only the lowest bit of
its mantissa set.
-/

namespace FirTest.FloatModel

/-- The format these cases run at. -/
private abbrev q : Float.Model.Format := f16

/-! # Addition -/

-- 1 + 1 = 2
#guard fadd q 0x3C00 0x3C00 == 0x4000
-- 1 + h is a tie: to the even 1
#guard fadd q 0x3C00 0x1000 == 0x3C00
-- (1 + u) + h is a tie: to the even 1 + 2u
#guard fadd q 0x3C01 0x1000 == 0x3C02
-- 1 + 3h/2 is past the tie: up to 1 + u
#guard fadd q 0x3C00 0x1200 == 0x3C01
-- 1 + h/2 is short of the tie: down to 1
#guard fadd q 0x3C00 0x0C00 == 0x3C00
-- M + M overflows to inf
#guard fadd q 0x7BFF 0x7BFF == 0x7C00
-- M + H is a tie at the top: to inf
#guard fadd q 0x7BFF 0x4C00 == 0x7C00
-- M + H/2 is short of the tie: M
#guard fadd q 0x7BFF 0x4800 == 0x7BFF
-- M + s = M: s is far below half an ulp of M
#guard fadd q 0x7BFF 0x0001 == 0x7BFF
-- s + s = 2s, subnormal and exact
#guard fadd q 0x0001 0x0001 == 0x0002
-- S + s = n, from subnormal to normal
#guard fadd q 0x03FF 0x0001 == 0x0400
-- 1 + -1 = +0
#guard fadd q 0x3C00 0xBC00 == 0x0000
-- -0 + -0 = -0
#guard fadd q 0x8000 0x8000 == 0x8000
-- +0 + -0 = +0
#guard fadd q 0x0000 0x8000 == 0x0000
-- -s + s = +0
#guard fadd q 0x8001 0x0001 == 0x0000
-- inf + -inf is NaN
#guard fadd q 0x7C00 0xFC00 == 0x7E00
-- -inf + M = -inf
#guard fadd q 0xFC00 0x7BFF == 0xFC00
-- a NaN with a payload and a sign gives the canonical NaN
#guard fadd q 0xFFFF 0x3C00 == 0x7E00
-- a signalling NaN gives the canonical NaN
#guard fadd q 0x3C00 0x7C01 == 0x7E00

/-! # Subtraction -/

-- 1 - 1 = +0
#guard fsub q 0x3C00 0x3C00 == 0x0000
-- -0 - +0 = -0
#guard fsub q 0x8000 0x0000 == 0x8000
-- +0 - +0 = +0
#guard fsub q 0x0000 0x0000 == 0x0000
-- n - s = S, from normal to subnormal
#guard fsub q 0x0400 0x0001 == 0x03FF
-- 1 - h/2 is a tie below 1: to the even 1
#guard fsub q 0x3C00 0x0C00 == 0x3C00
-- -M - M overflows to -inf
#guard fsub q 0xFBFF 0x7BFF == 0xFC00
-- inf - inf is NaN
#guard fsub q 0x7C00 0x7C00 == 0x7E00
-- +0 - inf = -inf
#guard fsub q 0x0000 0x7C00 == 0xFC00
-- a NaN operand gives the canonical NaN
#guard fsub q 0x3C00 0xFFFF == 0x7E00

/-! # Multiplication -/

-- 1.5 * 1.5 = 2.25
#guard fmul q 0x3E00 0x3E00 == 0x4080
-- (1 + u)^2 is short of the tie: down to 1 + 2u
#guard fmul q 0x3C01 0x3C01 == 0x3C02
-- n * 0.5 = n/2, subnormal and exact
#guard fmul q 0x0400 0x3800 == 0x0200
-- s * 0.5 is a tie: to the even +0
#guard fmul q 0x0001 0x3800 == 0x0000
-- 3s * 0.5 is a tie: to the even 2s
#guard fmul q 0x0003 0x3800 == 0x0002
-- s * 0.75 is past the tie: up to s
#guard fmul q 0x0001 0x3A00 == 0x0001
-- -s * 0.25 underflows to -0
#guard fmul q 0x8001 0x3400 == 0x8000
-- M * 2 overflows to inf
#guard fmul q 0x7BFF 0x4000 == 0x7C00
-- -M * M overflows to -inf
#guard fmul q 0xFBFF 0x7BFF == 0xFC00
-- s * s underflows far below s: to +0
#guard fmul q 0x0001 0x0001 == 0x0000
-- -s * S underflows far below s: to -0
#guard fmul q 0x8001 0x03FF == 0x8000
-- -0 * 1 = -0
#guard fmul q 0x8000 0x3C00 == 0x8000
-- +0 * inf is NaN
#guard fmul q 0x0000 0x7C00 == 0x7E00
-- -1 * inf = -inf
#guard fmul q 0xBC00 0x7C00 == 0xFC00
-- a NaN operand gives the canonical NaN
#guard fmul q 0xFFFF 0x0000 == 0x7E00

/-! # Division -/

-- 1 / 3, rounded to nearest
#guard fdiv q 0x3C00 0x4200 == 0x3555
-- 1 / (1 + u), rounded to nearest
#guard fdiv q 0x3C00 0x3C01 == 0x3BFE
-- 1 / +0 = inf
#guard fdiv q 0x3C00 0x0000 == 0x7C00
-- -1 / +0 = -inf
#guard fdiv q 0xBC00 0x0000 == 0xFC00
-- 1 / -0 = -inf
#guard fdiv q 0x3C00 0x8000 == 0xFC00
-- 0 / 0 is NaN
#guard fdiv q 0x0000 0x0000 == 0x7E00
-- inf / inf is NaN
#guard fdiv q 0x7C00 0x7C00 == 0x7E00
-- 1 / inf = +0
#guard fdiv q 0x3C00 0x7C00 == 0x0000
-- -1 / inf = -0
#guard fdiv q 0xBC00 0x7C00 == 0x8000
-- n / 2^m = s, exact
#guard fdiv q 0x0400 0x6400 == 0x0001
-- s / 2 is a tie: to the even +0
#guard fdiv q 0x0001 0x4000 == 0x0000
-- 3s / 2 is a tie: to the even 2s
#guard fdiv q 0x0003 0x4000 == 0x0002
-- M / 0.5 overflows to inf
#guard fdiv q 0x7BFF 0x3800 == 0x7C00
-- s / M underflows far below s: to +0
#guard fdiv q 0x0001 0x7BFF == 0x0000
-- M / s overflows to inf
#guard fdiv q 0x7BFF 0x0001 == 0x7C00
-- -0 / 1 = -0
#guard fdiv q 0x8000 0x3C00 == 0x8000
-- a NaN operand gives the canonical NaN
#guard fdiv q 0x3C00 0xFFFF == 0x7E00

/-! # Fused multiply-add -/

-- 1 * 1 + 1 = 2
#guard ffma q 0x3C00 0x3C00 0x3C00 == 0x4000
-- (1 + u)(1 - u) - 1 = -u^2: one rounding, not two
#guard ffma q 0x3C01 0x3BFE 0xBC00 == 0x8010
-- (1 + u)^2 - (1 + 2u) = u^2, exact
#guard ffma q 0x3C01 0x3C01 0xBC02 == 0x0010
-- M * 2 - M = M: the product does not overflow
#guard ffma q 0x7BFF 0x4000 0xFBFF == 0x7BFF
-- 1 * h + 1 is a tie: to the even 1
#guard ffma q 0x3C00 0x1000 0x3C00 == 0x3C00
-- s * 0.5 + 0 is a tie: to the even +0
#guard ffma q 0x0001 0x3800 0x0000 == 0x0000
-- +0 * 1 + -0 = +0
#guard ffma q 0x0000 0x3C00 0x8000 == 0x0000
-- -0 * 1 + -0 = -0
#guard ffma q 0x8000 0x3C00 0x8000 == 0x8000
-- -1 * 1 + 1 = +0
#guard ffma q 0xBC00 0x3C00 0x3C00 == 0x0000
-- inf * 0 + NaN is NaN
#guard ffma q 0x7C00 0x0000 0xFFFF == 0x7E00
-- inf * 1 - inf is NaN
#guard ffma q 0x7C00 0x3C00 0xFC00 == 0x7E00
-- 1 * 1 + inf = inf
#guard ffma q 0x3C00 0x3C00 0x7C00 == 0x7C00
-- s * s - s = -s: the product is far below half an ulp of s
#guard ffma q 0x0001 0x0001 0x8001 == 0x8001
-- M * M - inf = -inf
#guard ffma q 0x7BFF 0x7BFF 0xFC00 == 0xFC00

/-! # Square root -/

-- sqrt 4 = 2
#guard fsqrt q 0x4400 == 0x4000
-- sqrt 2.25 = 1.5
#guard fsqrt q 0x4080 == 0x3E00
-- sqrt 2, rounded to nearest
#guard fsqrt q 0x4000 == 0x3DA8
-- sqrt s, rounded to nearest
#guard fsqrt q 0x0001 == 0x0C00
-- sqrt M, rounded to nearest
#guard fsqrt q 0x7BFF == 0x5BFF
-- sqrt +0 = +0
#guard fsqrt q 0x0000 == 0x0000
-- sqrt -0 = -0
#guard fsqrt q 0x8000 == 0x8000
-- sqrt -1 is NaN
#guard fsqrt q 0xBC00 == 0x7E00
-- sqrt inf = inf
#guard fsqrt q 0x7C00 == 0x7C00
-- sqrt -inf is NaN
#guard fsqrt q 0xFC00 == 0x7E00
-- a NaN operand gives the canonical NaN
#guard fsqrt q 0xFFFF == 0x7E00

/-! # Negation and absolute value -/

-- neg +0 = -0
#guard fneg q 0x0000 == 0x8000
-- neg -inf = inf
#guard fneg q 0xFC00 == 0x7C00
-- neg s = -s
#guard fneg q 0x0001 == 0x8001
-- neg of a NaN is the canonical NaN, not the NaN with its sign flipped
#guard fneg q 0xFFFF == 0x7E00
-- abs -0 = +0
#guard fabs q 0x8000 == 0x0000
-- abs -M = M
#guard fabs q 0xFBFF == 0x7BFF
-- abs of a NaN is the canonical NaN
#guard fabs q 0xFFFF == 0x7E00

/-! # Constants: unpacking and packing -/

-- unpacking and packing s gives its bits back
#guard fbits q 0x0001 == 0x0001
-- unpacking and packing S gives its bits back
#guard fbits q 0x03FF == 0x03FF
-- unpacking and packing n gives its bits back
#guard fbits q 0x0400 == 0x0400
-- unpacking and packing M gives its bits back
#guard fbits q 0x7BFF == 0x7BFF
-- unpacking and packing -0 gives its bits back
#guard fbits q 0x8000 == 0x8000
-- unpacking and packing -inf gives its bits back
#guard fbits q 0xFC00 == 0xFC00
-- unpacking and packing -1 gives its bits back
#guard fbits q 0xBC00 == 0xBC00
-- unpacking and packing a NaN gives the canonical NaN
#guard fbits q 0xFFFF == 0x7E00
-- unpacking and packing a signalling NaN gives the canonical NaN
#guard fbits q 0x7C01 == 0x7E00

/-! # Comparison -/

-- +0 and -0 are equal
#guard fcmp q 0x0000 0x8000 == some .eq
-- NaN is unordered with itself
#guard fcmp q 0x7E00 0x7E00 == none
-- NaN is unordered with 1
#guard fcmp q 0xFFFF 0x3C00 == none
-- -inf < s
#guard fcmp q 0xFC00 0x0001 == some .lt
-- M < inf
#guard fcmp q 0x7BFF 0x7C00 == some .lt
-- 1 < 1 + u
#guard fcmp q 0x3C00 0x3C01 == some .lt
-- -1 > -2
#guard fcmp q 0xBC00 0xC000 == some .gt
-- s < S
#guard fcmp q 0x0001 0x03FF == some .lt
-- -s < +0
#guard fcmp q 0x8001 0x0000 == some .lt
-- -0 < s
#guard fcmp q 0x8000 0x0001 == some .lt
-- inf = inf
#guard fcmp q 0x7C00 0x7C00 == some .eq

end FirTest.FloatModel
