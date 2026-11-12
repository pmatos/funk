# The runtime helper that does frem and fmod at f32 and f64 (#310). SSE has
# no remainder, so each op is a call of a routine below. The backend
# appends this file, once, to the assembly of a module in which a function
# does frem or fmod at f32 or f64, so the module's object file carries it,
# as it does the helpers of fma and of division at i128
# (docs/decisions/x86-64-backend-lowering.md#the-remainders).
#
# Each routine is a System V function of two floats that returns one: x in
# %xmm0, y in %xmm1, and the remainder in %xmm0. Every symbol is local to
# the object file, with no .globl, and starts with __funk_rt_, which no fir
# function's symbol does (ADR-2026-10-30-1232). The routines use only %rax,
# %xmm0 and the x87 stack, which System V lets a callee clobber and which
# each routine leaves empty, and 16 bytes of stack below the caller's
# %rsp: the return address and the one push.
#
# The remainder comes from the x87 unit, which every x86-64 has. fprem1 is
# IEEE 754's remainder: x - n * y with n the quotient x / y rounded to
# nearest, ties to even. fprem is C's fmod, with n truncated toward zero.
# Each reduces the exponent of x by at most 63 at a time and sets C2, bit
# 10 of the status word, while the reduction is partial, so the routine
# runs it until C2 is clear. Both are exact, whatever the x87 precision
# control says, and loading an f32 or f64, its subnormals included, is
# exact too. The remainder is a multiple of the smaller quantum of x and y
# no larger than |y|, so the format holds it and the store to f32 or f64
# is exact. A zero remainder has the sign of x, a finite x with an
# infinite y gives x, and y = 0 or an infinite x gives a NaN. A NaN result
# may be any NaN (ADR-2026-11-09-1549), so the routines take no care over
# which one they give. The x87 exceptions stay masked, as System V starts
# them, so none traps.

	.text

# __funk_rt_fremf(x, y) at f32: IEEE 754's remainder.
	.type	__funk_rt_fremf, @function
	.p2align	4
__funk_rt_fremf:
	pushq	%rax			# room for one float
	movss	%xmm1, (%rsp)
	flds	(%rsp)			# y
	movss	%xmm0, (%rsp)
	flds	(%rsp)			# x, above y
.Lrt_fremf_loop:
	fprem1
	fnstsw	%ax
	testb	$4, %ah			# C2: the reduction is partial
	jnz	.Lrt_fremf_loop
	fstp	%st(1)			# drop y, keep the remainder
	fstps	(%rsp)
	movss	(%rsp), %xmm0
	popq	%rax
	ret
	.size	__funk_rt_fremf, .-__funk_rt_fremf

# __funk_rt_frem(x, y) at f64: IEEE 754's remainder.
	.type	__funk_rt_frem, @function
	.p2align	4
__funk_rt_frem:
	pushq	%rax
	movsd	%xmm1, (%rsp)
	fldl	(%rsp)
	movsd	%xmm0, (%rsp)
	fldl	(%rsp)
.Lrt_frem_loop:
	fprem1
	fnstsw	%ax
	testb	$4, %ah
	jnz	.Lrt_frem_loop
	fstp	%st(1)
	fstpl	(%rsp)
	movsd	(%rsp), %xmm0
	popq	%rax
	ret
	.size	__funk_rt_frem, .-__funk_rt_frem

# __funk_rt_fmodf(x, y) at f32: C's fmod.
	.type	__funk_rt_fmodf, @function
	.p2align	4
__funk_rt_fmodf:
	pushq	%rax
	movss	%xmm1, (%rsp)
	flds	(%rsp)
	movss	%xmm0, (%rsp)
	flds	(%rsp)
.Lrt_fmodf_loop:
	fprem
	fnstsw	%ax
	testb	$4, %ah
	jnz	.Lrt_fmodf_loop
	fstp	%st(1)
	fstps	(%rsp)
	movss	(%rsp), %xmm0
	popq	%rax
	ret
	.size	__funk_rt_fmodf, .-__funk_rt_fmodf

# __funk_rt_fmod(x, y) at f64: C's fmod.
	.type	__funk_rt_fmod, @function
	.p2align	4
__funk_rt_fmod:
	pushq	%rax
	movsd	%xmm1, (%rsp)
	fldl	(%rsp)
	movsd	%xmm0, (%rsp)
	fldl	(%rsp)
.Lrt_fmod_loop:
	fprem
	fnstsw	%ax
	testb	$4, %ah
	jnz	.Lrt_fmod_loop
	fstp	%st(1)
	fstpl	(%rsp)
	movsd	(%rsp), %xmm0
	popq	%rax
	ret
	.size	__funk_rt_fmod, .-__funk_rt_fmod
