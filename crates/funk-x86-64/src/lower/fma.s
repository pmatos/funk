# The runtime helper that does fma at f32 and f64 (#229). SSE has no fused
# multiply-add, so fma is a call of a routine below. The backend appends
# this file, once, to the assembly of a module in which a function does
# fma at f32 or f64, so the module's object file carries it, as it does
# the helper that divides at i128
# (docs/decisions/x86-64-backend-lowering-floats.md#float-arithmetic).
#
# Each routine is a System V function of three floats that returns one:
# a in %xmm0, b in %xmm1, c in %xmm2, and a * b + c, rounded once to
# nearest even, in %xmm0. Every symbol is local to the object file, with
# no .globl, and starts with __funk_rt_, which no fir function's symbol
# does (ADR-2026-10-30-1232). The routines use only %rax, %rcx, %rdx,
# %rsi, %rdi, %r8 to %r11 and %xmm0 to %xmm2, which System V lets a callee
# clobber, and 16 bytes of stack below the caller's %rsp at most: the
# return address, and the one push of __funk_rt_fmaf or the return
# address of __funk_rt_fma's call of .Lrt_fma_unpack.
#
# A NaN result may be any NaN (ADR-2026-11-09-1549), so the routines take
# no care over which one they give.

	.text

# __funk_rt_fmaf(a, b, c) at f32. Each operand widens to f64 exactly. The
# product of two f32 has at most 48 bits, so f64 holds it exactly, and
# neither overflows nor underflows there. The sum is rounded to odd in f64,
# by rounding toward zero and setting the last bit when the sum was
# inexact, and then to nearest even in f32. Rounding to odd with at least
# two more bits than the target, then to the target, rounds once (Boldo
# and Melquiond, "Emulation of FMA and correctly rounded sums: proved
# algorithms using rounding to odd", 2008), so the result is a * b + c
# rounded once. The routine sets the rounding mode of MXCSR to toward
# zero for the one addition, and restores MXCSR, its flags included,
# before the narrowing.
	.type	__funk_rt_fmaf, @function
	.p2align	4
__funk_rt_fmaf:
	cvtss2sd	%xmm0, %xmm0
	cvtss2sd	%xmm1, %xmm1
	cvtss2sd	%xmm2, %xmm2
	mulsd	%xmm1, %xmm0		# a * b, exact
	pushq	%rax			# room for two MXCSR values
	stmxcsr	(%rsp)
	movl	(%rsp), %eax
	orl	$0x6000, %eax		# rounding control: toward zero
	andl	$-33, %eax		# clear the inexact flag, bit 5
	movl	%eax, 4(%rsp)
	ldmxcsr	4(%rsp)
	addsd	%xmm2, %xmm0		# a * b + c, toward zero
	stmxcsr	4(%rsp)
	ldmxcsr	(%rsp)
	testl	$32, 4(%rsp)
	jz	.Lrt_fmaf_exact
	movq	%xmm0, %rax
	orq	$1, %rax		# inexact: round to odd
	movq	%rax, %xmm0
.Lrt_fmaf_exact:
	popq	%rax
	cvtsd2ss	%xmm0, %xmm0
	ret
	.size	__funk_rt_fmaf, .-__funk_rt_fmaf

# __funk_rt_fma(a, b, c) at f64. No wider format holds the product of two
# f64, so the routine computes a * b + c exactly in integers and rounds it
# once.
#
# Special operands first. A NaN or infinite a or b gives what SSE's
# a * b + c gives: a NaN, or the infinity of the product when c is not the
# opposite infinity, and the product of an infinity and a finite number
# never overflows wrongly. Otherwise a NaN or infinite c is the result. A
# zero a or b makes the product an exact zero, so SSE's a * b + c is
# exact too, and a zero c makes the result a * b rounded once, the sign of
# a product that rounds to zero included.
#
# Then a, b and c are finite and not zero. Each is m * 2^e with m of 53
# bits, its top bit set: a subnormal's mantissa is shifted up. The product
# P = ma * mb has 105 or 106 bits, and goes in a 128-bit integer shifted
# left 21 bits; c goes in one shifted left 74 bits. So each has its top
# bit at bit 125 or 126 and at least 21 zero bits at the bottom. The one
# with the smaller exponent is shifted right to the other's, and any bit it
# loses sets its lowest bit (a jam). The other one's lowest bit is zero, so
# the sum or difference has a lowest bit that is set exactly when bits
# were lost, and the jam lies far below where the result rounds: a shift
# loses bits only past 21 bits, and then the difference cancels at most
# one leading bit. The two are added, or subtracted when their signs
# differ, the smaller from the larger, which gives the sign. An exact zero
# is +0, as IEEE 754 rounds to nearest. The sum S * 2^e then rounds once to
# 53 bits, or fewer for a subnormal result: the quantum is 2^q with
# q = max(top - 52, -1074), for the exponent top of the top bit of S. The
# bit below the quantum is the guard bit, any bit below that makes the sum
# inexact, and the sum rounds up when the guard bit is set and it is
# inexact or the kept mantissa m is odd. The result's bits are then
# (q + 1074) * 2^52 + m: for a normal m the implicit bit adds one to the
# exponent field, and a carry out of the mantissa does the same. A result
# that reaches the exponent field of the infinities is the infinity.
	.type	__funk_rt_fma, @function
	.p2align	4
__funk_rt_fma:
	movq	%xmm0, %rdi		# a
	movq	%xmm1, %rsi		# b
	movq	%xmm2, %rdx		# c
	movabsq	$0x7ff0000000000000, %r8
	movq	%rdi, %rax
	andq	%r8, %rax
	cmpq	%r8, %rax
	je	.Lrt_fma_sse		# a is a NaN or infinite
	movq	%rsi, %rax
	andq	%r8, %rax
	cmpq	%r8, %rax
	je	.Lrt_fma_sse		# b is a NaN or infinite
	movq	%rdx, %rax
	andq	%r8, %rax
	cmpq	%r8, %rax
	je	.Lrt_fma_c		# c is a NaN or infinite
	movq	%rdi, %rax
	addq	%rax, %rax
	jz	.Lrt_fma_sse		# a is a zero
	movq	%rsi, %rax
	addq	%rax, %rax
	jz	.Lrt_fma_sse		# b is a zero
	movq	%rdx, %rax
	addq	%rax, %rax
	jz	.Lrt_fma_product	# c is a zero
	# The signs: bit 63 of %r10 is the product's, and bit 0 is set when
	# c's differs from it, so that the magnitudes subtract.
	movq	%rdi, %r10
	xorq	%rsi, %r10
	shrq	$63, %r10
	shlq	$63, %r10		# the product's sign
	movq	%rdx, %r11
	xorq	%r10, %r11
	shrq	$63, %r11
	orq	%r11, %r10		# and whether c's differs
	movq	%rdx, %r11		# c, for later
	# ma in %rdi with ea in %r8, mb in %rsi with eb in %rcx.
	movq	%rdi, %rax
	call	.Lrt_fma_unpack
	movq	%rax, %rdi
	movq	%rcx, %r8
	movq	%rsi, %rax
	call	.Lrt_fma_unpack
	movq	%rax, %rsi
	addq	%rcx, %r8		# the product's exponent
	movq	%rdi, %rax
	mulq	%rsi			# P = ma * mb in %rdx:%rax
	shldq	$21, %rax, %rdx
	shlq	$21, %rax
	subq	$21, %r8
	movq	%rdx, %rsi		# P, high half
	movq	%rax, %rdi		# P, low half
	movq	%r11, %rax
	call	.Lrt_fma_unpack		# mc in %rax, ec in %rcx
	movq	%rax, %r9
	shlq	$10, %r9		# c, high half
	xorl	%edx, %edx		# c, low half
	subq	$74, %rcx		# c's exponent
	# Keep the operand with the larger exponent in %rsi:%rdi, with its
	# exponent in %r8 and its sign in bit 63 of %r10, and shift the other,
	# in %r9:%rdx, right by the difference.
	movq	%r8, %rax
	subq	%rcx, %rax
	jge	.Lrt_fma_align
	xchgq	%rsi, %r9
	xchgq	%rdi, %rdx
	movq	%rcx, %r8
	negq	%rax
	testb	$1, %r10b
	jz	.Lrt_fma_align
	btcq	$63, %r10		# c's sign, the opposite of the product's
.Lrt_fma_align:
	movq	%rax, %rcx
	cmpq	$128, %rcx
	jb	.Lrt_fma_below128
	xorl	%r9d, %r9d		# every bit is lost: only the jam is left
	movl	$1, %edx
	jmp	.Lrt_fma_sum
.Lrt_fma_below128:
	cmpq	$64, %rcx
	jb	.Lrt_fma_below64
	subl	$64, %ecx
	movq	%r9, %rax
	shrq	%cl, %rax		# the new low half
	movq	%rax, %r11
	shlq	%cl, %r11
	xorq	%r9, %r11		# the bits of the high half that are lost
	orq	%rdx, %r11		# and the whole low half
	movq	%rax, %rdx
	xorl	%r9d, %r9d
	jmp	.Lrt_fma_jam
.Lrt_fma_below64:
	testq	%rcx, %rcx
	jz	.Lrt_fma_sum
	movq	%rdx, %rax
	shrq	%cl, %rax
	shlq	%cl, %rax
	movq	%rdx, %r11
	xorq	%rax, %r11		# the bits of the low half that are lost
	shrdq	%cl, %r9, %rdx
	shrq	%cl, %r9
.Lrt_fma_jam:
	testq	%r11, %r11
	jz	.Lrt_fma_sum
	orq	$1, %rdx
.Lrt_fma_sum:
	testb	$1, %r10b
	jnz	.Lrt_fma_subtract
	addq	%rdx, %rdi
	adcq	%r9, %rsi		# S = X + Y, below 2^128
	jmp	.Lrt_fma_round
.Lrt_fma_subtract:
	subq	%rdx, %rdi
	sbbq	%r9, %rsi		# S = X - Y
	jnc	.Lrt_fma_nonnegative
	notq	%rsi			# Y was larger: negate S and its sign
	negq	%rdi
	sbbq	$-1, %rsi
	btcq	$63, %r10
.Lrt_fma_nonnegative:
	movq	%rsi, %rax
	orq	%rdi, %rax
	jz	.Lrt_fma_zero
.Lrt_fma_round:
	# The top bit of S, in %rax.
	bsrq	%rdi, %rax
	testq	%rsi, %rsi
	jz	.Lrt_fma_top
	bsrq	%rsi, %rax
	addq	$64, %rax
.Lrt_fma_top:
	addq	%r8, %rax		# its exponent
	subq	$52, %rax		# q, before the subnormal bound
	movq	$-1074, %rcx
	cmpq	%rcx, %rax
	cmovlq	%rcx, %rax		# q
	movq	%rax, %rcx
	subq	%r8, %rcx		# the bits below the quantum
	movq	%rax, %r8		# q
	jg	.Lrt_fma_inexact
	negq	%rcx			# S is exact at q: S < 2^53
	shlq	%cl, %rdi		# m
	jmp	.Lrt_fma_pack
.Lrt_fma_inexact:
	# The trailing zeros of S, in %r11.
	bsfq	%rdi, %r11
	testq	%rdi, %rdi
	jnz	.Lrt_fma_trailing
	bsfq	%rsi, %r11
	addq	$64, %r11
.Lrt_fma_trailing:
	decq	%rcx			# the guard bit's place
	cmpq	%rcx, %r11		# a set bit below it?
	setb	%r11b
	movzbl	%r11b, %r11d
	cmpq	$64, %rcx
	jb	.Lrt_fma_shift_low
	subl	$64, %ecx
	movq	%rsi, %rdi
	shrq	%cl, %rdi
	jmp	.Lrt_fma_guard
.Lrt_fma_shift_low:
	shrdq	%cl, %rsi, %rdi		# S shifted to its guard bit
.Lrt_fma_guard:
	movq	%rdi, %rax
	shrq	$1, %rdi		# m
	andl	$1, %eax		# the guard bit
	jz	.Lrt_fma_pack
	movl	%edi, %ecx
	andl	$1, %ecx		# m is odd
	orq	%rcx, %r11
	jz	.Lrt_fma_pack		# a tie, to the even m
	incq	%rdi
.Lrt_fma_pack:
	addq	$1074, %r8
	shlq	$52, %r8
	addq	%r8, %rdi
	movabsq	$0x7ff0000000000000, %rax
	cmpq	%rax, %rdi
	cmovaeq	%rax, %rdi		# overflow: the infinity
	btrq	$0, %r10
	orq	%r10, %rdi		# the sign
	movq	%rdi, %xmm0
	ret
.Lrt_fma_zero:
	xorps	%xmm0, %xmm0
	ret
.Lrt_fma_sse:
	mulsd	%xmm1, %xmm0
	addsd	%xmm2, %xmm0
	ret
.Lrt_fma_product:
	mulsd	%xmm1, %xmm0
	ret
.Lrt_fma_c:
	movapd	%xmm2, %xmm0
	ret
	.size	__funk_rt_fma, .-__funk_rt_fma

# The mantissa and exponent of the finite nonzero f64 in %rax: its value
# is m * 2^e, with m in %rax, its bit 52 set, and e in %rcx. Uses %r9.
	.p2align	4
.Lrt_fma_unpack:
	movq	%rax, %rcx
	shrq	$52, %rcx
	andl	$0x7ff, %ecx		# the exponent field
	movabsq	$0xfffffffffffff, %r9
	andq	%r9, %rax
	testl	%ecx, %ecx
	jz	.Lrt_fma_subnormal
	btsq	$52, %rax
	subq	$1075, %rcx
	ret
.Lrt_fma_subnormal:
	bsrq	%rax, %r9
	movl	$52, %ecx
	subl	%r9d, %ecx
	shlq	%cl, %rax
	negq	%rcx
	subq	$1074, %rcx
	ret
