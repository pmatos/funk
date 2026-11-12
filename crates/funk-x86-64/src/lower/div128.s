# The runtime helper that divides at i128 (#22). The backend appends this
# file, once, to the assembly of a module in which a function divides at
# i128, so the module's object file carries it
# (docs/decisions/x86-64-backend-lowering.md#division-at-i128).
#
# Each of sdiv, udiv, srem and urem at i128 is a call of its own routine
# below. Every symbol is local to the object file, with no .globl, and
# starts with __funk_rt_, which no fir function's symbol does
# (ADR-2026-10-30-1232). Each routine is a System V function of two
# __int128 arguments that returns an __int128: a in %rdi (its low half)
# and %rsi (its high half), b in %rdx and %rcx, and the result in %rax and
# %rdx, written high:low below. It uses only %rax, %rcx, %rdx, %rsi, %rdi
# and %r8 to %r11, which System V lets a callee clobber, and 24 bytes of
# stack below the caller's %rsp at most: its return address, the sign that
# the signed ones push, and their calls of __funk_rt_magnitudes and
# __funk_rt_udivmod128
# (docs/decisions/x86-64-backend-lowering.md#division-at-i128).
#
# No routine tests its divisor. A zero divisor traps in the first divq, as
# a division at i64 traps, and sdiv and srem of the signed minimum by -1
# give some value; both are immediate UB in the source
# (ADR-2026-10-29-2006), which any behaviour refines.

	.text

# __funk_rt_udivmod128(a, b) -> the quotient a / b in %rdx:%rax and the
# remainder a % b in %rsi:%rdi, both read as unsigned.
	.type	__funk_rt_udivmod128, @function
	.p2align	4
__funk_rt_udivmod128:
	movq	%rdx, %r8		# b, low half
	movq	%rcx, %r9		# b, high half
	testq	%r9, %r9
	jnz	.Lrt_div128_wide
	# b < 2^64: long division by one 64-bit digit. The first divq gives
	# the quotient's high half and a remainder below b, so the second,
	# of that remainder and a's low half, fits in 64 bits.
	movq	%rsi, %rax
	xorl	%edx, %edx
	divq	%r8
	movq	%rax, %r9		# the quotient, high half
	movq	%rdi, %rax
	divq	%r8
	movq	%rdx, %rdi
	xorl	%esi, %esi
	movq	%r9, %rdx
	ret
.Lrt_div128_wide:
	# b >= 2^64, so a's high half is below b and the quotient fits in 64
	# bits. Restoring division of a's low half, one bit a step: the
	# remainder r in %r11:%r10 starts as a's high half, and each step
	# shifts the next bit of a into r from the top of %rdi, and the next
	# bit of the quotient into the bottom of %rdi. r never passes the bits
	# of a shifted into it, so it never carries out of 128 bits.
	movq	%rsi, %r10
	xorl	%r11d, %r11d
	movl	$64, %ecx
.Lrt_div128_step:
	addq	%rdi, %rdi
	adcq	%r10, %r10
	adcq	%r11, %r11
	cmpq	%r8, %r10
	movq	%r11, %rax
	sbbq	%r9, %rax
	jb	.Lrt_div128_next	# r < b
	subq	%r8, %r10
	sbbq	%r9, %r11
	incq	%rdi
.Lrt_div128_next:
	decl	%ecx
	jnz	.Lrt_div128_step
	movq	%rdi, %rax
	xorl	%edx, %edx
	movq	%r10, %rdi
	movq	%r11, %rsi
	ret
	.size	__funk_rt_udivmod128, .-__funk_rt_udivmod128

# __funk_rt_udiv128(a, b) -> a / b, read as unsigned.
	.type	__funk_rt_udiv128, @function
	.p2align	4
__funk_rt_udiv128:
	jmp	__funk_rt_udivmod128
	.size	__funk_rt_udiv128, .-__funk_rt_udiv128

# __funk_rt_urem128(a, b) -> a % b, read as unsigned.
	.type	__funk_rt_urem128, @function
	.p2align	4
__funk_rt_urem128:
	call	__funk_rt_udivmod128
	movq	%rdi, %rax
	movq	%rsi, %rdx
	ret
	.size	__funk_rt_urem128, .-__funk_rt_urem128

# __funk_rt_sdiv128(a, b) -> a / b, read as signed and rounded towards
# zero: the unsigned quotient of their magnitudes, negated when their
# signs differ. A sign is 0 or -1, and (x ^ s) - s is x when s is 0 and
# -x when s is -1.
	.type	__funk_rt_sdiv128, @function
	.p2align	4
__funk_rt_sdiv128:
	call	__funk_rt_magnitudes
	xorq	%r9, %r8		# the quotient's sign
	pushq	%r8
	call	__funk_rt_udivmod128
	popq	%r8
	xorq	%r8, %rax
	xorq	%r8, %rdx
	subq	%r8, %rax
	sbbq	%r8, %rdx
	ret
	.size	__funk_rt_sdiv128, .-__funk_rt_sdiv128

# __funk_rt_srem128(a, b) -> a % b, read as signed: the unsigned remainder
# of their magnitudes, with the sign of a.
	.type	__funk_rt_srem128, @function
	.p2align	4
__funk_rt_srem128:
	call	__funk_rt_magnitudes
	pushq	%r8			# the remainder's sign: a's
	call	__funk_rt_udivmod128
	popq	%r8
	movq	%rdi, %rax
	movq	%rsi, %rdx
	xorq	%r8, %rax
	xorq	%r8, %rdx
	subq	%r8, %rax
	sbbq	%r8, %rdx
	ret
	.size	__funk_rt_srem128, .-__funk_rt_srem128

# __funk_rt_magnitudes(a, b), with a and b where the routines above take
# them: replaces each with its magnitude, read as unsigned, and returns the
# sign of a in %r8 and that of b in %r9. The magnitude of the signed
# minimum is 2^127.
	.type	__funk_rt_magnitudes, @function
	.p2align	4
__funk_rt_magnitudes:
	movq	%rsi, %r8
	sarq	$63, %r8
	movq	%rcx, %r9
	sarq	$63, %r9
	xorq	%r8, %rdi
	xorq	%r8, %rsi
	subq	%r8, %rdi
	sbbq	%r8, %rsi
	xorq	%r9, %rdx
	xorq	%r9, %rcx
	subq	%r9, %rdx
	sbbq	%r9, %rcx
	ret
	.size	__funk_rt_magnitudes, .-__funk_rt_magnitudes
