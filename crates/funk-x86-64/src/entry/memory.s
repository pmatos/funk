# The runtime's memory report
# (docs/decisions/x86-64-backend-executable.md#reporting-memory): with
# `--memory`, after the function returns, the values line also gives every
# global of the module, its address and its units. This file follows
# values.s in the entry file, and uses the routines and data of runtime.s.
#
# The table `__funk_globals` is in the module's own file, where a global
# that is not `export` is a local symbol: its number of globals, then for
# each the report's text up to the address, that text's length, the
# global's address and its size. A module without globals defines no
# table, so the weak reference below reads 0 and the list is empty.

	.weak	__funk_globals

	.text

# __funk_rt_globals(): adds `,"memory":[...]` to standard output's buffer,
# each global as {"global":"@g","memory":N,"address":"A","units":"U"}.
__funk_rt_globals:
	pushq	%rbx
	pushq	%r12
	subq	$56, %rsp
	leaq	.Lmemory_open(%rip), %rdi
	movl	$(.Lmemory_open_end - .Lmemory_open), %esi
	call	__funk_rt_out
	movq	.Lglobals(%rip), %rbx
	xorl	%r12d, %r12d
	testq	%rbx, %rbx
	jz	1f
	movq	(%rbx), %r12		# the number of globals
	addq	$8, %rbx
1:	testq	%r12, %r12
	jz	2f
	movq	(%rbx), %rdi		# the text up to the address
	movq	8(%rbx), %rsi
	call	__funk_rt_out
	movq	16(%rbx), %rdi		# the address, printed as an i64 is
	movq	%rdi, %rsi
	sarq	$63, %rsi
	leaq	48(%rsp), %rdx
	call	__funk_rt_format
	movq	%rax, %rdi
	leaq	48(%rsp), %rsi
	subq	%rax, %rsi
	call	__funk_rt_out
	leaq	.Lunits_open(%rip), %rdi
	movl	$(.Lunits_open_end - .Lunits_open), %esi
	call	__funk_rt_out
	movq	16(%rbx), %rdi
	movq	24(%rbx), %rsi
	call	__funk_rt_units
	leaq	.Lunits_close(%rip), %rdi
	movl	$(.Lunits_close_end - .Lunits_close), %esi
	call	__funk_rt_out
	addq	$32, %rbx
	decq	%r12
	jmp	1b
2:	leaq	.Lmemory_close(%rip), %rdi
	movl	$1, %esi
	call	__funk_rt_out
	addq	$56, %rsp
	popq	%r12
	popq	%rbx
	ret

# __funk_rt_units(bytes, len): adds the `len` bytes at `bytes` to standard
# output's buffer, each as two lower-case hexadecimal digits, except that a
# run of 16 or more zero bytes is written zeros(N).
__funk_rt_units:
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	subq	$48, %rsp
	movq	%rdi, %rbx		# the next byte
	leaq	(%rdi,%rsi), %r12	# the end
1:	cmpq	%r12, %rbx
	jae	5f
	movq	%rbx, %r13		# the end of the zeros from here
2:	cmpq	%r12, %r13
	jae	3f
	cmpb	$0, (%r13)
	jne	3f
	incq	%r13
	jmp	2b
3:	movq	%r13, %rax
	subq	%rbx, %rax
	cmpq	$16, %rax
	jb	4f
	leaq	.Lzeros(%rip), %rdi
	movl	$(.Lzeros_end - .Lzeros), %esi
	call	__funk_rt_out
	movq	%r13, %rdi
	subq	%rbx, %rdi
	xorl	%esi, %esi
	leaq	48(%rsp), %rdx
	call	__funk_rt_format
	movq	%rax, %rdi
	leaq	48(%rsp), %rsi
	subq	%rax, %rsi
	call	__funk_rt_out
	leaq	.Lzeros_close(%rip), %rdi
	movl	$1, %esi
	call	__funk_rt_out
	movq	%r13, %rbx
	jmp	1b
4:	movzbl	(%rbx), %eax
	leaq	.Lhex(%rip), %rdx
	movl	%eax, %ecx
	shrl	$4, %ecx
	movzbl	(%rdx,%rcx), %ecx
	movb	%cl, (%rsp)
	andl	$15, %eax
	movzbl	(%rdx,%rax), %eax
	movb	%al, 1(%rsp)
	movq	%rsp, %rdi
	movl	$2, %esi
	call	__funk_rt_out
	incq	%rbx
	jmp	1b
5:	addq	$48, %rsp
	popq	%r13
	popq	%r12
	popq	%rbx
	ret

	.section	.rodata
.Lmemory_open:	.ascii	",\"memory\":["
.Lmemory_open_end:
.Lmemory_close:	.ascii	"]"
.Lunits_open:	.ascii	"\",\"units\":\""
.Lunits_open_end:
.Lunits_close:	.ascii	"\"}"
.Lunits_close_end:
.Lzeros:	.ascii	"zeros("
.Lzeros_end:
.Lzeros_close:	.ascii	")"
.Lopt_memory:	.ascii	"--memory"
.Lopt_memory_end:

# The table's address, or 0 when the module defines none. A word of data,
# not a reference relative to %rip, so that the weak symbol resolves the
# same way in a static and in a dynamically linked program.
	.data
	.p2align	3
.Lglobals:	.quad	__funk_globals
