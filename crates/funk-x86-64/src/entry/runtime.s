# The runtime of an executable that `funk build` links (ADR-2026-10-30-1233).
#
# The executable runs one function of the module: `PROGRAM @FUNCTION ARG...`.
# The runtime finds the function in the table `__funk_functions`, which the
# entry generator writes after this file, checks the argument count, and
# calls the function's wrapper. The wrapper parses each argument with
# `__funk_rt_arg`, calls the function, and prints each result with
# `__funk_rt_value`. The runtime then prints the line {"values":[...]} on
# standard output and exits with 0. A bad command line is reported on
# standard error, with exit status 2.
#
# It uses no libc: only the Linux system calls write (1) and exit_group (231).
# Every routine follows the System V AMD64 calling convention.

	.text

# The entry point. The kernel leaves argc at (%rsp), then argv, with %rsp
# 16-byte aligned.
	.globl	__funk_start
	.type	__funk_start, @function
__funk_start:
	xorl	%ebp, %ebp
	movq	(%rsp), %rdi
	leaq	8(%rsp), %rsi
	call	__funk_rt_main
	ud2
	.size	__funk_start, .-__funk_start

# __funk_rt_main(argc, argv). Never returns.
__funk_rt_main:
	pushq	%rbp
	movq	%rsp, %rbp
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	movq	(%rsi), %rax
	testq	%rax, %rax
	jnz	1f
	leaq	.Lprogram_default(%rip), %rax
1:	movq	%rax, __funk_rt_program(%rip)
	cmpq	$2, %rdi
	jb	.Lusage
	leaq	-2(%rdi), %r12
	movq	8(%rsi), %r13
	leaq	16(%rsi), %rax
	movq	%rax, __funk_rt_args(%rip)
	leaq	__funk_functions(%rip), %rbx
	movq	(%rbx), %r14
	addq	$8, %rbx
.Lfind:
	testq	%r14, %r14
	jz	.Lunknown
	movq	%r13, %rdi
	movq	(%rbx), %rsi
	movq	8(%rbx), %rdx
	call	__funk_rt_equal
	testl	%eax, %eax
	jnz	.Lfound
	addq	$32, %rbx
	decq	%r14
	jmp	.Lfind
.Lfound:
	cmpq	16(%rbx), %r12
	jne	.Lcount
	leaq	.Lopen(%rip), %rdi
	movl	$(.Lopen_end - .Lopen), %esi
	call	__funk_rt_out
	call	*24(%rbx)
	leaq	.Lclose(%rip), %rdi
	movl	$(.Lclose_end - .Lclose), %esi
	call	__funk_rt_out
	call	__funk_rt_flush
	xorl	%edi, %edi
	jmp	__funk_rt_exit
.Lusage:
	leaq	.Lmsg_usage(%rip), %rdi
	call	__funk_rt_err_cstr
	movq	__funk_rt_program(%rip), %rdi
	call	__funk_rt_err_cstr
	leaq	.Lmsg_usage_args(%rip), %rdi
	jmp	.Ldie
.Lunknown:
	call	__funk_rt_err_program
	leaq	.Lmsg_no_function(%rip), %rdi
	call	__funk_rt_err_cstr
	movq	%r13, %rdi
	call	__funk_rt_err_cstr
	leaq	.Lmsg_in_program(%rip), %rdi
	jmp	.Ldie
.Lcount:
	call	__funk_rt_err_program
	movq	%r13, %rdi
	call	__funk_rt_err_cstr
	leaq	.Lmsg_takes(%rip), %rdi
	call	__funk_rt_err_cstr
	movq	16(%rbx), %rdi
	call	__funk_rt_err_num
	leaq	.Lmsg_arguments_not(%rip), %rdi
	call	__funk_rt_err_cstr
	movq	%r12, %rdi
	call	__funk_rt_err_num
	leaq	.Lmsg_newline(%rip), %rdi
.Ldie:
	call	__funk_rt_err_cstr
	movl	$2, %edi
	jmp	__funk_rt_exit

# __funk_rt_arg(index, width) -> the value of argument `index` of the
# function, parsed as a value of `iW`. Exits with 2 if it is not one.
__funk_rt_arg:
	pushq	%rbx
	pushq	%r12
	subq	$8, %rsp
	movl	%esi, %r12d
	movq	__funk_rt_args(%rip), %rax
	movq	(%rax,%rdi,8), %rbx
	movq	%rbx, %rdi
	call	__funk_rt_parse
	testl	%edx, %edx
	jz	1f
	addq	$8, %rsp
	popq	%r12
	popq	%rbx
	ret
1:	call	__funk_rt_err_program
	movq	%rbx, %rdi
	call	__funk_rt_err_cstr
	leaq	.Lmsg_not_value(%rip), %rdi
	call	__funk_rt_err_cstr
	movq	%r12, %rdi
	call	__funk_rt_err_num
	leaq	.Lmsg_newline(%rip), %rdi
	jmp	.Ldie

# __funk_rt_parse(text, width) -> %rax = the value, %edx = 1; or %edx = 0
# when `text` is not the spelling of a value of `iW`: true or false at i1,
# and otherwise a signed decimal with no leading zeros, no `+` and no `-0`,
# from -2^(W-1) to 2^(W-1)-1. W is from 1 to 64.
__funk_rt_parse:
	cmpl	$1, %esi
	jne	.Lparse_int
	leaq	.Ltrue(%rip), %rsi
	movl	$(.Ltrue_end - .Ltrue), %edx
	call	__funk_rt_equal
	testl	%eax, %eax
	jz	1f
	movl	$1, %edx
	ret
1:	leaq	.Lfalse(%rip), %rsi
	movl	$(.Lfalse_end - .Lfalse), %edx
	call	__funk_rt_equal
	movl	%eax, %edx
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
	movl	$1, %edx
	ret
2:	subl	$49, %ecx		# the first digit is 1 to 9
	cmpl	$8, %ecx
	ja	.Lparse_fail
	xorl	%eax, %eax
	movl	$10, %r9d
3:	movzbl	(%rdi), %ecx
	testl	%ecx, %ecx
	jz	4f
	subl	$48, %ecx
	cmpl	$9, %ecx
	ja	.Lparse_fail
	mulq	%r9
	jc	.Lparse_fail
	addq	%rcx, %rax
	jc	.Lparse_fail
	incq	%rdi
	jmp	3b
4:	leal	-1(%rsi), %ecx		# the bound 2^(W-1)
	movl	$1, %edx
	shlq	%cl, %rdx
	testl	%r8d, %r8d
	jnz	5f
	cmpq	%rdx, %rax
	jae	.Lparse_fail
	movl	$1, %edx
	ret
5:	cmpq	%rdx, %rax
	ja	.Lparse_fail
	negq	%rax
	movl	$1, %edx
	ret
.Lparse_fail:
	xorl	%eax, %eax
	xorl	%edx, %edx
	ret

# __funk_rt_value(value, width): prints one result, after a comma unless it
# is the first: "true" or "false" at i1, by bit 0, and otherwise the signed
# decimal of `value`, which the wrapper has sign-extended from W bits.
__funk_rt_value:
	pushq	%rbx
	pushq	%r12
	subq	$40, %rsp
	movq	%rdi, %rbx
	movl	%esi, %r12d
	movq	__funk_rt_count(%rip), %rax
	incq	__funk_rt_count(%rip)
	testq	%rax, %rax
	jz	1f
	leaq	.Lcomma(%rip), %rdi
	movl	$1, %esi
	call	__funk_rt_out
1:	leaq	.Lquote(%rip), %rdi
	movl	$1, %esi
	call	__funk_rt_out
	cmpl	$1, %r12d
	jne	3f
	leaq	.Ltrue(%rip), %rdi
	movl	$(.Ltrue_end - .Ltrue), %esi
	testb	$1, %bl
	jnz	2f
	leaq	.Lfalse(%rip), %rdi
	movl	$(.Lfalse_end - .Lfalse), %esi
2:	call	__funk_rt_out
	jmp	4f
3:	movq	%rbx, %rdi
	leaq	32(%rsp), %rsi
	call	__funk_rt_format
	movq	%rax, %rdi
	leaq	32(%rsp), %rsi
	subq	%rax, %rsi
	call	__funk_rt_out
4:	leaq	.Lquote(%rip), %rdi
	movl	$1, %esi
	call	__funk_rt_out
	addq	$40, %rsp
	popq	%r12
	popq	%rbx
	ret

# __funk_rt_format(value, end) -> the start of the signed decimal of
# `value`, written into the bytes just before `end`: at most 20.
__funk_rt_format:
	movq	%rdi, %rax
	movq	%rsi, %r8
	movl	$10, %ecx
	testq	%rax, %rax
	jns	1f
	negq	%rax			# the magnitude; 2^63 for the minimum
1:	xorl	%edx, %edx
	divq	%rcx
	addl	$48, %edx		# '0'
	decq	%r8
	movb	%dl, (%r8)
	testq	%rax, %rax
	jnz	1b
	testq	%rdi, %rdi
	jns	2f
	decq	%r8
	movb	$45, (%r8)		# '-'
2:	movq	%r8, %rax
	ret

# __funk_rt_equal(cstr, bytes, len) -> 1 when the NUL-terminated `cstr`
# holds exactly the `len` bytes at `bytes`, else 0. Changes only %rax,
# %rcx and %r8.
__funk_rt_equal:
	xorl	%eax, %eax
	xorl	%ecx, %ecx
1:	cmpq	%rdx, %rcx
	je	2f
	movzbl	(%rdi,%rcx), %r8d
	cmpb	(%rsi,%rcx), %r8b
	jne	3f
	incq	%rcx
	jmp	1b
2:	cmpb	$0, (%rdi,%rcx)
	sete	%al
3:	ret

# __funk_rt_out(bytes, len): adds bytes to standard output's buffer.
__funk_rt_out:
	movq	__funk_rt_out_len(%rip), %rax
	leaq	(%rax,%rsi), %rcx
	cmpq	$4096, %rcx
	jbe	2f
	pushq	%rdi
	pushq	%rsi
	subq	$8, %rsp
	call	__funk_rt_flush
	addq	$8, %rsp
	popq	%rsi
	popq	%rdi
	cmpq	$4096, %rsi
	jbe	1f
	movq	%rsi, %rdx
	movq	%rdi, %rsi
	movl	$1, %edi
	jmp	__funk_rt_write
1:	xorl	%eax, %eax
2:	movq	%rsi, %rcx
	movq	%rdi, %rsi
	leaq	__funk_rt_out_buf(%rip), %rdi
	addq	%rax, %rdi
	addq	%rcx, __funk_rt_out_len(%rip)
	rep movsb
	ret

# __funk_rt_flush(): writes the buffer to standard output.
__funk_rt_flush:
	movq	__funk_rt_out_len(%rip), %rdx
	movq	$0, __funk_rt_out_len(%rip)
	leaq	__funk_rt_out_buf(%rip), %rsi
	movl	$1, %edi
	jmp	__funk_rt_write

# __funk_rt_write(fd, bytes, len): writes all the bytes, or exits with 2.
__funk_rt_write:
1:	testq	%rdx, %rdx
	jz	3f
	movl	$1, %eax		# write
	syscall
	cmpq	$-4, %rax		# EINTR: try again
	je	1b
	testq	%rax, %rax
	jle	2f
	addq	%rax, %rsi
	subq	%rax, %rdx
	jmp	1b
2:	movl	$2, %edi
	jmp	__funk_rt_exit
3:	ret

# __funk_rt_exit(status). Never returns.
__funk_rt_exit:
	movl	$231, %eax		# exit_group
	syscall
	ud2

# __funk_rt_err_program(): writes "PROGRAM: " to standard error.
__funk_rt_err_program:
	subq	$8, %rsp
	movq	__funk_rt_program(%rip), %rdi
	call	__funk_rt_err_cstr
	leaq	.Lmsg_colon(%rip), %rdi
	addq	$8, %rsp
	jmp	__funk_rt_err_cstr

# __funk_rt_err_cstr(cstr): writes a NUL-terminated string to standard
# error.
__funk_rt_err_cstr:
	xorl	%edx, %edx
1:	cmpb	$0, (%rdi,%rdx)
	je	2f
	incq	%rdx
	jmp	1b
2:	movq	%rdi, %rsi
	movl	$2, %edi
	jmp	__funk_rt_write

# __funk_rt_err_num(n): writes the signed decimal of `n` to standard error.
__funk_rt_err_num:
	subq	$40, %rsp
	leaq	32(%rsp), %rsi
	call	__funk_rt_format
	movq	%rax, %rsi
	leaq	32(%rsp), %rdx
	subq	%rax, %rdx
	movl	$2, %edi
	call	__funk_rt_write
	addq	$40, %rsp
	ret

	.section	.rodata
.Ltrue:	.ascii	"true"
.Ltrue_end:
.Lfalse:	.ascii	"false"
.Lfalse_end:
.Lopen:	.ascii	"{\"values\":["
.Lopen_end:
.Lclose:	.ascii	"]}\n"
.Lclose_end:
.Lcomma:	.ascii	","
.Lquote:	.ascii	"\""
.Lprogram_default:	.asciz	"program"
.Lmsg_usage:	.asciz	"usage: "
.Lmsg_usage_args:	.asciz	" @FUNCTION ARG...\n"
.Lmsg_colon:	.asciz	": "
.Lmsg_no_function:	.asciz	"no function "
.Lmsg_in_program:	.asciz	" in this program\n"
.Lmsg_takes:	.asciz	" takes "
.Lmsg_arguments_not:	.asciz	" arguments, not "
.Lmsg_not_value:	.asciz	" is not a value of type i"
.Lmsg_newline:	.asciz	"\n"

	.bss
	.p2align	4
__funk_rt_out_buf:	.skip	4096
__funk_rt_out_len:	.skip	8
__funk_rt_count:	.skip	8
__funk_rt_program:	.skip	8
__funk_rt_args:	.skip	8
