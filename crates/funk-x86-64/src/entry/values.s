# The runtime's values (ADR-2026-10-30-1233): it reads each argument of a
# function from the command line, and prints each result, at every width
# that the backend lowers, i1 to i128. This file follows runtime.s in the
# entry file, and uses its routines and its data.
#
# Every routine works on 128 bits. A value of at most 64 bits is the low
# half, sign-extended to 64 bits; an i128 is a pair of halves, the low one
# in one register and the high one in another (ADR-2026-11-03-0107).

	.text

# __funk_rt_arg(index, width) -> the value of argument `index` of the
# function, parsed as a value of `iW`: in %rax, and at i128 its high half
# in %rdx. Exits with 2 if it is not one.
__funk_rt_arg:
	pushq	%rbx
	pushq	%r12
	subq	$8, %rsp
	movl	%esi, %r12d
	movq	__funk_rt_args(%rip), %rax
	movq	(%rax,%rdi,8), %rbx
	movq	%rbx, %rdi
	call	__funk_rt_parse
	testl	%ecx, %ecx
	jz	1f
	addq	$8, %rsp
	popq	%r12
	popq	%rbx
	ret
1:	call	__funk_rt_err_program
	movq	%rbx, %rdi
	call	__funk_rt_err_text
	leaq	.Lmsg_not_value(%rip), %rdi
	call	__funk_rt_err_cstr
	movq	%r12, %rdi
	call	__funk_rt_err_num
	leaq	.Lmsg_newline(%rip), %rdi
	jmp	.Ldie

# __funk_rt_parse(text, width) -> %rax = the low half of the value,
# %rdx = its high half, %ecx = 1; or %ecx = 0 when `text` is not the
# spelling of a value of `iW`: true or false at i1, 1 or 0 in %rax, and
# otherwise a signed decimal with no leading zeros, no `+` and no `-0`,
# from -2^(W-1) to 2^(W-1)-1, sign-extended to 128 bits. W is from 1 to
# 128. The magnitude is read into %r10:%r9, and a text whose magnitude
# does not fit 128 bits is not a value.
__funk_rt_parse:
	cmpl	$1, %esi
	jne	.Lparse_int
	leaq	.Ltrue(%rip), %rsi
	movl	$(.Ltrue_end - .Ltrue), %edx
	call	__funk_rt_equal
	testl	%eax, %eax
	jz	1f
	movl	%eax, %ecx
	ret
1:	leaq	.Lfalse(%rip), %rsi
	movl	$(.Lfalse_end - .Lfalse), %edx
	call	__funk_rt_equal
	movl	%eax, %ecx
	xorl	%eax, %eax
	ret
.Lparse_int:
	xorl	%r8d, %r8d
	cmpb	$45, (%rdi)		# '-'
	jne	1f
	movl	$1, %r8d
	incq	%rdi
1:	movzbl	(%rdi), %ecx
	cmpl	$48, %ecx		# '0': only "0" itself
	jne	2f
	testl	%r8d, %r8d
	jnz	.Lparse_fail
	cmpb	$0, 1(%rdi)
	jne	.Lparse_fail
	xorl	%eax, %eax
	xorl	%edx, %edx
	movl	$1, %ecx
	ret
2:	subl	$49, %ecx		# the first digit is 1 to 9
	cmpl	$8, %ecx
	ja	.Lparse_fail
	xorl	%r9d, %r9d
	xorl	%r10d, %r10d
	movl	$10, %r11d
3:	movzbl	(%rdi), %ecx
	testl	%ecx, %ecx
	jz	4f
	subl	$48, %ecx
	cmpl	$9, %ecx
	ja	.Lparse_fail
	movq	%r10, %rax		# the magnitude times 10: its high half,
	mulq	%r11			# which must fit 64 bits,
	jc	.Lparse_fail
	movq	%rax, %r10
	movq	%r9, %rax		# then its low half, which carries into
	mulq	%r11			# the high one
	addq	%rdx, %r10
	jc	.Lparse_fail
	addq	%rcx, %rax		# and the digit
	adcq	$0, %r10
	jc	.Lparse_fail
	movq	%rax, %r9
	incq	%rdi
	jmp	3b
4:	leal	-1(%rsi), %ecx		# the bound 2^(W-1), in %rdx:%rax
	xorl	%eax, %eax
	xorl	%edx, %edx
	cmpl	$64, %ecx
	jae	5f
	movl	$1, %eax
	shlq	%cl, %rax
	jmp	6f
5:	movl	$1, %edx		# the count is masked to W - 65
	shlq	%cl, %rdx
6:	testl	%r8d, %r8d
	jnz	7f
	cmpq	%rax, %r9		# a positive magnitude is below the bound:
	movq	%r10, %rcx		# subtracting the bound borrows
	sbbq	%rdx, %rcx
	jae	.Lparse_fail
	movq	%r9, %rax
	movq	%r10, %rdx
	movl	$1, %ecx
	ret
7:	cmpq	%r9, %rax		# a negative one is at most the bound:
	sbbq	%r10, %rdx		# subtracting it from the bound does not
	jb	.Lparse_fail		# borrow
	xorl	%eax, %eax		# the value, 0 minus the magnitude
	xorl	%edx, %edx
	subq	%r9, %rax
	sbbq	%r10, %rdx
	movl	$1, %ecx
	ret
.Lparse_fail:
	xorl	%eax, %eax
	xorl	%edx, %edx
	xorl	%ecx, %ecx
	ret

# __funk_rt_value(value, width, high): prints one result, after a comma
# unless it is the first: "true" or "false" at i1, by bit 0, and otherwise
# its signed decimal. Below i128, `value` is the result, which the wrapper
# has sign-extended from W bits, and `high` is not read; at i128, `value`
# is its low half and `high` its high half.
__funk_rt_value:
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	subq	$48, %rsp
	movq	%rdi, %rbx
	movl	%esi, %r12d
	movq	%rdx, %r13
	cmpl	$128, %esi
	je	1f
	movq	%rdi, %r13		# the high half of a narrower value: its
	sarq	$63, %r13		# sign
1:	movq	__funk_rt_count(%rip), %rax
	incq	__funk_rt_count(%rip)
	testq	%rax, %rax
	jz	2f
	leaq	.Lcomma(%rip), %rdi
	movl	$1, %esi
	call	__funk_rt_out
2:	leaq	.Lquote(%rip), %rdi
	movl	$1, %esi
	call	__funk_rt_out
	cmpl	$1, %r12d
	jne	4f
	leaq	.Ltrue(%rip), %rdi
	movl	$(.Ltrue_end - .Ltrue), %esi
	testb	$1, %bl
	jnz	3f
	leaq	.Lfalse(%rip), %rdi
	movl	$(.Lfalse_end - .Lfalse), %esi
3:	call	__funk_rt_out
	jmp	5f
4:	movq	%rbx, %rdi
	movq	%r13, %rsi
	leaq	48(%rsp), %rdx
	call	__funk_rt_format
	movq	%rax, %rdi
	leaq	48(%rsp), %rsi
	subq	%rax, %rsi
	call	__funk_rt_out
5:	leaq	.Lquote(%rip), %rdi
	movl	$1, %esi
	call	__funk_rt_out
	addq	$48, %rsp
	popq	%r13
	popq	%r12
	popq	%rbx
	ret

# __funk_rt_format(low, high, end) -> the start of the signed decimal of
# the 128-bit value high:low, written into the bytes just before `end`: at
# most 40. Each digit comes from dividing the magnitude, in %r10:%r9, by
# 10: its high half first, then the remainder and its low half, so that
# neither division overflows.
__funk_rt_format:
	movq	%rdx, %r8
	movq	%rdi, %r9
	movq	%rsi, %r10
	testq	%rsi, %rsi
	jns	1f
	negq	%r9			# the magnitude; 2^127 for the minimum
	adcq	$0, %r10
	negq	%r10
1:	movl	$10, %ecx
2:	xorl	%edx, %edx
	movq	%r10, %rax
	divq	%rcx
	movq	%rax, %r10
	movq	%r9, %rax
	divq	%rcx
	movq	%rax, %r9
	addl	$48, %edx		# '0'
	decq	%r8
	movb	%dl, (%r8)
	movq	%r9, %rax
	orq	%r10, %rax
	jnz	2b
	testq	%rsi, %rsi
	jns	3f
	decq	%r8
	movb	$45, (%r8)		# '-'
3:	movq	%r8, %rax
	ret

	.section	.rodata
.Ltrue:	.ascii	"true"
.Ltrue_end:
.Lfalse:	.ascii	"false"
.Lfalse_end:
.Lcomma:	.ascii	","
.Lquote:	.ascii	"\""
.Lmsg_not_value:	.asciz	" is not a value of type i"
