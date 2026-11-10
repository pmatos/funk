import FirTest.FloatModel

/-!
Known answers for Lean's float model at `bf16`, `float<8,7>`, on the hard
inputs: ties, subnormals, `-0`, overflow to infinity and NaN operands
(#229). Each expected bit pattern was computed apart from Lean's code,
with exact rational arithmetic, and each case's comment says what the
result is. The symbols: `u` is an ulp of 1, `2^-7`, and `h` is `u/2`;
`s` is the smallest subnormal, `S` the largest subnormal, `n` the
smallest normal number, `M` the largest finite number, and `H` half an
ulp of `M`. A NaN result is the model's one canonical NaN. The NaN
operand "with a payload and a sign" has every bit set, and the
signalling NaN has only the lowest bit of its mantissa set.
-/

namespace FirTest.FloatModel

/-- The format these cases run at. -/
private abbrev q : Float.Model.Format := bf16

/-! # Addition -/

-- 1 + 1 = 2
#guard fadd q 0x3F80 0x3F80 == 0x4000
-- 1 + h is a tie: to the even 1
#guard fadd q 0x3F80 0x3B80 == 0x3F80
-- (1 + u) + h is a tie: to the even 1 + 2u
#guard fadd q 0x3F81 0x3B80 == 0x3F82
-- 1 + 3h/2 is past the tie: up to 1 + u
#guard fadd q 0x3F80 0x3BC0 == 0x3F81
-- 1 + h/2 is short of the tie: down to 1
#guard fadd q 0x3F80 0x3B00 == 0x3F80
-- M + M overflows to inf
#guard fadd q 0x7F7F 0x7F7F == 0x7F80
-- M + H is a tie at the top: to inf
#guard fadd q 0x7F7F 0x7B00 == 0x7F80
-- M + H/2 is short of the tie: M
#guard fadd q 0x7F7F 0x7A80 == 0x7F7F
-- M + s = M: s is far below half an ulp of M
#guard fadd q 0x7F7F 0x0001 == 0x7F7F
-- s + s = 2s, subnormal and exact
#guard fadd q 0x0001 0x0001 == 0x0002
-- S + s = n, from subnormal to normal
#guard fadd q 0x007F 0x0001 == 0x0080
-- 1 + -1 = +0
#guard fadd q 0x3F80 0xBF80 == 0x0000
-- -0 + -0 = -0
#guard fadd q 0x8000 0x8000 == 0x8000
-- +0 + -0 = +0
#guard fadd q 0x0000 0x8000 == 0x0000
-- -s + s = +0
#guard fadd q 0x8001 0x0001 == 0x0000
-- inf + -inf is NaN
#guard fadd q 0x7F80 0xFF80 == 0x7FC0
-- -inf + M = -inf
#guard fadd q 0xFF80 0x7F7F == 0xFF80
-- a NaN with a payload and a sign gives the canonical NaN
#guard fadd q 0xFFFF 0x3F80 == 0x7FC0
-- a signalling NaN gives the canonical NaN
#guard fadd q 0x3F80 0x7F81 == 0x7FC0

/-! # Subtraction -/

-- 1 - 1 = +0
#guard fsub q 0x3F80 0x3F80 == 0x0000
-- -0 - +0 = -0
#guard fsub q 0x8000 0x0000 == 0x8000
-- +0 - +0 = +0
#guard fsub q 0x0000 0x0000 == 0x0000
-- n - s = S, from normal to subnormal
#guard fsub q 0x0080 0x0001 == 0x007F
-- 1 - h/2 is a tie below 1: to the even 1
#guard fsub q 0x3F80 0x3B00 == 0x3F80
-- -M - M overflows to -inf
#guard fsub q 0xFF7F 0x7F7F == 0xFF80
-- inf - inf is NaN
#guard fsub q 0x7F80 0x7F80 == 0x7FC0
-- +0 - inf = -inf
#guard fsub q 0x0000 0x7F80 == 0xFF80
-- a NaN operand gives the canonical NaN
#guard fsub q 0x3F80 0xFFFF == 0x7FC0

/-! # Multiplication -/

-- 1.5 * 1.5 = 2.25
#guard fmul q 0x3FC0 0x3FC0 == 0x4010
-- (1 + u)^2 is short of the tie: down to 1 + 2u
#guard fmul q 0x3F81 0x3F81 == 0x3F82
-- n * 0.5 = n/2, subnormal and exact
#guard fmul q 0x0080 0x3F00 == 0x0040
-- s * 0.5 is a tie: to the even +0
#guard fmul q 0x0001 0x3F00 == 0x0000
-- 3s * 0.5 is a tie: to the even 2s
#guard fmul q 0x0003 0x3F00 == 0x0002
-- s * 0.75 is past the tie: up to s
#guard fmul q 0x0001 0x3F40 == 0x0001
-- -s * 0.25 underflows to -0
#guard fmul q 0x8001 0x3E80 == 0x8000
-- M * 2 overflows to inf
#guard fmul q 0x7F7F 0x4000 == 0x7F80
-- -M * M overflows to -inf
#guard fmul q 0xFF7F 0x7F7F == 0xFF80
-- s * s underflows far below s: to +0
#guard fmul q 0x0001 0x0001 == 0x0000
-- -s * S underflows far below s: to -0
#guard fmul q 0x8001 0x007F == 0x8000
-- -0 * 1 = -0
#guard fmul q 0x8000 0x3F80 == 0x8000
-- +0 * inf is NaN
#guard fmul q 0x0000 0x7F80 == 0x7FC0
-- -1 * inf = -inf
#guard fmul q 0xBF80 0x7F80 == 0xFF80
-- a NaN operand gives the canonical NaN
#guard fmul q 0xFFFF 0x0000 == 0x7FC0

/-! # Division -/

-- 1 / 3, rounded to nearest
#guard fdiv q 0x3F80 0x4040 == 0x3EAB
-- 1 / (1 + u), rounded to nearest
#guard fdiv q 0x3F80 0x3F81 == 0x3F7E
-- 1 / +0 = inf
#guard fdiv q 0x3F80 0x0000 == 0x7F80
-- -1 / +0 = -inf
#guard fdiv q 0xBF80 0x0000 == 0xFF80
-- 1 / -0 = -inf
#guard fdiv q 0x3F80 0x8000 == 0xFF80
-- 0 / 0 is NaN
#guard fdiv q 0x0000 0x0000 == 0x7FC0
-- inf / inf is NaN
#guard fdiv q 0x7F80 0x7F80 == 0x7FC0
-- 1 / inf = +0
#guard fdiv q 0x3F80 0x7F80 == 0x0000
-- -1 / inf = -0
#guard fdiv q 0xBF80 0x7F80 == 0x8000
-- n / 2^m = s, exact
#guard fdiv q 0x0080 0x4300 == 0x0001
-- s / 2 is a tie: to the even +0
#guard fdiv q 0x0001 0x4000 == 0x0000
-- 3s / 2 is a tie: to the even 2s
#guard fdiv q 0x0003 0x4000 == 0x0002
-- M / 0.5 overflows to inf
#guard fdiv q 0x7F7F 0x3F00 == 0x7F80
-- s / M underflows far below s: to +0
#guard fdiv q 0x0001 0x7F7F == 0x0000
-- M / s overflows to inf
#guard fdiv q 0x7F7F 0x0001 == 0x7F80
-- -0 / 1 = -0
#guard fdiv q 0x8000 0x3F80 == 0x8000
-- a NaN operand gives the canonical NaN
#guard fdiv q 0x3F80 0xFFFF == 0x7FC0

/-! # Fused multiply-add -/

-- 1 * 1 + 1 = 2
#guard ffma q 0x3F80 0x3F80 0x3F80 == 0x4000
-- (1 + u)(1 - u) - 1 = -u^2: one rounding, not two
#guard ffma q 0x3F81 0x3F7E 0xBF80 == 0xB880
-- (1 + u)^2 - (1 + 2u) = u^2, exact
#guard ffma q 0x3F81 0x3F81 0xBF82 == 0x3880
-- M * 2 - M = M: the product does not overflow
#guard ffma q 0x7F7F 0x4000 0xFF7F == 0x7F7F
-- 1 * h + 1 is a tie: to the even 1
#guard ffma q 0x3F80 0x3B80 0x3F80 == 0x3F80
-- s * 0.5 + 0 is a tie: to the even +0
#guard ffma q 0x0001 0x3F00 0x0000 == 0x0000
-- +0 * 1 + -0 = +0
#guard ffma q 0x0000 0x3F80 0x8000 == 0x0000
-- -0 * 1 + -0 = -0
#guard ffma q 0x8000 0x3F80 0x8000 == 0x8000
-- -1 * 1 + 1 = +0
#guard ffma q 0xBF80 0x3F80 0x3F80 == 0x0000
-- inf * 0 + NaN is NaN
#guard ffma q 0x7F80 0x0000 0xFFFF == 0x7FC0
-- inf * 1 - inf is NaN
#guard ffma q 0x7F80 0x3F80 0xFF80 == 0x7FC0
-- 1 * 1 + inf = inf
#guard ffma q 0x3F80 0x3F80 0x7F80 == 0x7F80
-- s * s - s = -s: the product is far below half an ulp of s
#guard ffma q 0x0001 0x0001 0x8001 == 0x8001
-- M * M - inf = -inf
#guard ffma q 0x7F7F 0x7F7F 0xFF80 == 0xFF80

/-! # Square root -/

-- sqrt 4 = 2
#guard fsqrt q 0x4080 == 0x4000
-- sqrt 2.25 = 1.5
#guard fsqrt q 0x4010 == 0x3FC0
-- sqrt 2, rounded to nearest
#guard fsqrt q 0x4000 == 0x3FB5
-- sqrt s, rounded to nearest
#guard fsqrt q 0x0001 == 0x1E35
-- sqrt 2s = 2^-66, exact
#guard fsqrt q 0x0002 == 0x1E80
-- sqrt M, rounded to nearest
#guard fsqrt q 0x7F7F == 0x5F7F
-- sqrt +0 = +0
#guard fsqrt q 0x0000 == 0x0000
-- sqrt -0 = -0
#guard fsqrt q 0x8000 == 0x8000
-- sqrt -1 is NaN
#guard fsqrt q 0xBF80 == 0x7FC0
-- sqrt inf = inf
#guard fsqrt q 0x7F80 == 0x7F80
-- sqrt -inf is NaN
#guard fsqrt q 0xFF80 == 0x7FC0
-- a NaN operand gives the canonical NaN
#guard fsqrt q 0xFFFF == 0x7FC0

/-! # Negation and absolute value -/

-- neg +0 = -0
#guard fneg q 0x0000 == 0x8000
-- neg -inf = inf
#guard fneg q 0xFF80 == 0x7F80
-- neg s = -s
#guard fneg q 0x0001 == 0x8001
-- neg of a NaN is the canonical NaN, not the NaN with its sign flipped
#guard fneg q 0xFFFF == 0x7FC0
-- abs -0 = +0
#guard fabs q 0x8000 == 0x0000
-- abs -M = M
#guard fabs q 0xFF7F == 0x7F7F
-- abs of a NaN is the canonical NaN
#guard fabs q 0xFFFF == 0x7FC0

/-! # Unpacking and packing -/

-- unpacking and packing s gives its bits back
#guard fbits q 0x0001 == 0x0001
-- unpacking and packing S gives its bits back
#guard fbits q 0x007F == 0x007F
-- unpacking and packing n gives its bits back
#guard fbits q 0x0080 == 0x0080
-- unpacking and packing M gives its bits back
#guard fbits q 0x7F7F == 0x7F7F
-- unpacking and packing -0 gives its bits back
#guard fbits q 0x8000 == 0x8000
-- unpacking and packing -inf gives its bits back
#guard fbits q 0xFF80 == 0xFF80
-- unpacking and packing -1 gives its bits back
#guard fbits q 0xBF80 == 0xBF80
-- unpacking and packing a NaN gives the canonical NaN
#guard fbits q 0xFFFF == 0x7FC0
-- unpacking and packing a signalling NaN gives the canonical NaN
#guard fbits q 0x7F81 == 0x7FC0

/-! # Comparison -/

-- +0 and -0 are equal
#guard fcmp q 0x0000 0x8000 == some .eq
-- NaN is unordered with itself
#guard fcmp q 0x7FC0 0x7FC0 == none
-- NaN is unordered with 1
#guard fcmp q 0xFFFF 0x3F80 == none
-- -inf < s
#guard fcmp q 0xFF80 0x0001 == some .lt
-- M < inf
#guard fcmp q 0x7F7F 0x7F80 == some .lt
-- 1 < 1 + u
#guard fcmp q 0x3F80 0x3F81 == some .lt
-- -1 > -2
#guard fcmp q 0xBF80 0xC000 == some .gt
-- s < S
#guard fcmp q 0x0001 0x007F == some .lt
-- -s < +0
#guard fcmp q 0x8001 0x0000 == some .lt
-- -0 < s
#guard fcmp q 0x8000 0x0001 == some .lt
-- inf = inf
#guard fcmp q 0x7F80 0x7F80 == some .eq

end FirTest.FloatModel
