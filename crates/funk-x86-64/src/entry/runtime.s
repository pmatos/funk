# The runtime of an executable that `funk build` links
# (docs/decisions/x86-64-backend-executable.md#running-one-function).
#
# The executable runs one function of the module: `PROGRAM @FUNCTION ARG...`.
# The runtime finds the function in the table `__funk_functions`, which the
# entry generator writes after this file, and checks the argument count. It
# reserves the stack that the table gives for the function, which covers
# every call it makes, or for a recursive function up to the process's stack
# limit (docs/decisions/x86-64-backend-executable.md#the-runs-stack), with a
# guard page below it, and calls the function's wrapper on that stack. The
# wrapper parses each argument with `__funk_rt_arg`, calls the function, and
# prints each result with `__funk_rt_value`, both in values.s, which follows
# this file. The runtime then prints the line {"values":[...]} on standard
# output and exits with 0. A bad command line, a stack that cannot be
# reserved, or a run that outgrows its stack is reported in one line on
# standard error, with exit status 2.
#
# It uses no libc: only the Linux system calls write (1), mmap (9),
# mprotect (10), rt_sigaction (13), rt_sigprocmask (14), rt_sigreturn (15),
# getpid (39), kill (62), getrlimit (97), sysinfo (99), sigaltstack (131)
# and exit_group (231). Every routine follows the System V AMD64 calling
# convention.
#
# When the module calls into the C library, `funk build` links with it and
# defines .Lfunk_libc before this file
# (docs/decisions/x86-64-backend.md#linking-with-the-host-c-library). Then
# the runtime also registers the dynamic loader's finalizer with
# __cxa_atexit, flushes the C library's streams with fflush(NULL) before it
# writes standard output, so what the function wrote comes first, and leaves
# a successful run through exit(0). Every other way out stays exit_group.

	.text

# The entry point. The kernel leaves argc at (%rsp), then argv, with %rsp
# 16-byte aligned. SIGPIPE is ignored, so a write to a pipe that nobody
# reads fails, and the program exits with 2 as on any failed write.
	.globl	__funk_start
	.type	__funk_start, @function
__funk_start:
	xorl	%ebp, %ebp
.ifdef .Lfunk_libc
	testq	%rdx, %rdx		# the dynamic loader's finalizer, if any
	jz	1f
	movq	%rdx, %rdi
	xorl	%esi, %esi
	xorl	%edx, %edx
	call	__cxa_atexit
1:
.endif
	movl	$13, %edi		# SIGPIPE
	leaq	.Lsig_ignore(%rip), %rsi
	xorl	%edx, %edx
	movl	$8, %r10d		# the size of a signal set
	movl	$13, %eax		# rt_sigaction
	syscall
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
	addq	$48, %rbx		# the next entry of the table
	decq	%r14
	jmp	.Lfind
.Lfound:
	cmpq	16(%rbx), %r12
	jne	.Lcount
	movq	32(%rbx), %r12		# the stack the run needs, or the least
	cmpq	$0, 40(%rbx)		# it gets when the function is recursive:
	je	.Lreserve		# then up to the process's stack limit
	call	__funk_rt_recursive_stack
	cmpq	%r12, %rax
	jbe	.Lreserve
	movq	%rax, %r12
.Lreserve:
	leaq	4096(%r12), %rsi	# the stack, and a guard page below it
	xorl	%edi, %edi
	movl	$3, %edx		# PROT_READ | PROT_WRITE
	movl	$0x24022, %r10d		# MAP_PRIVATE | MAP_ANONYMOUS
					# | MAP_NORESERVE | MAP_STACK
	movq	$-1, %r8
	xorl	%r9d, %r9d
	movl	$9, %eax		# mmap
	syscall
	cmpq	$-4095, %rax
	jb	.Lreserved
	cmpq	32(%rbx), %r12		# refused: try half as much, but never
	jbe	.Lno_stack		# less than the run needs
	shrq	$1, %r12
	andq	$-4096, %r12
	cmpq	32(%rbx), %r12
	jae	.Lreserve
	movq	32(%rbx), %r12
	jmp	.Lreserve
.Lreserved:
	movq	%rax, %r14
	movq	%rax, %rdi
	movl	$4096, %esi
	xorl	%edx, %edx		# PROT_NONE
	movl	$10, %eax		# mprotect
	syscall
	testq	%rax, %rax
	jnz	.Lno_stack
	movq	%r14, __funk_rt_guard(%rip)
	movq	%r12, __funk_rt_stack(%rip)
	movq	%r13, __funk_rt_function(%rip)
	call	__funk_rt_catch_overflow
	leaq	.Lopen(%rip), %rdi
	movl	$(.Lopen_end - .Lopen), %esi
	call	__funk_rt_out
	leaq	4096(%r14,%r12), %rsp	# the top of the reserved stack
	call	*24(%rbx)
	leaq	-32(%rbp), %rsp		# back on the process's stack
	leaq	.Lclose(%rip), %rdi
	movl	$(.Lclose_end - .Lclose), %esi
	call	__funk_rt_out
	call	__funk_rt_flush
	xorl	%edi, %edi
.ifdef .Lfunk_libc
	call	exit
.endif
	jmp	__funk_rt_exit
.Lusage:
	leaq	.Lmsg_usage(%rip), %rdi
	call	__funk_rt_err_cstr
	movq	__funk_rt_program(%rip), %rdi
	call	__funk_rt_err_text
	leaq	.Lmsg_usage_args(%rip), %rdi
	jmp	.Ldie
.Lunknown:
	call	__funk_rt_err_program
	leaq	.Lmsg_no_function(%rip), %rdi
	call	__funk_rt_err_cstr
	movq	%r13, %rdi
	call	__funk_rt_err_text
	leaq	.Lmsg_in_program(%rip), %rdi
	jmp	.Ldie
.Lno_stack:
	call	__funk_rt_err_program
	leaq	.Lmsg_no_stack(%rip), %rdi
	call	__funk_rt_err_cstr
	movq	32(%rbx), %rdi
	call	__funk_rt_err_num
	leaq	.Lmsg_stack_for(%rip), %rdi
	call	__funk_rt_err_cstr
	movq	%r13, %rdi
	call	__funk_rt_err_text
	leaq	.Lmsg_newline(%rip), %rdi
	jmp	.Ldie
.Lcount:
	call	__funk_rt_err_program
	movq	%r13, %rdi
	call	__funk_rt_err_text
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

# __funk_rt_recursive_stack() -> the bytes of stack that a recursive run
# may reserve: the soft limit on the process's stack (ulimit -s, by
# getrlimit), rounded down to a page, or the machine's memory and swap when
# they are less. A recursive run follows ulimit -s, as a C or Rust program
# does (docs/decisions/x86-64-backend-executable.md#the-runs-stack): 8 MiB
# by default, so a recursion without end reports at once that it ran out,
# instead of filling memory and swap first. ulimit -s unlimited
# (RLIM_INFINITY, all ones) leaves memory and swap as the bound, so fir
# keeps no depth limit of its own; so does a failed getrlimit.
__funk_rt_recursive_stack:
	pushq	%rbx
	subq	$16, %rsp		# a struct rlimit: rlim_cur, rlim_max
	movl	$3, %edi		# RLIMIT_STACK
	movq	%rsp, %rsi
	movl	$97, %eax		# getrlimit
	syscall
	movq	$-1, %rbx		# RLIM_INFINITY
	testq	%rax, %rax
	jnz	1f
	movq	(%rsp), %rbx		# rlim_cur, the soft limit
	andq	$-4096, %rbx
1:	call	__funk_rt_memory
	cmpq	%rbx, %rax
	cmovaq	%rbx, %rax
	addq	$16, %rsp
	popq	%rbx
	ret

# __funk_rt_memory() -> the bytes of memory and swap that the machine has,
# by sysinfo, rounded down to a page and at most 2^62; 0 if sysinfo fails.
__funk_rt_memory:
	subq	$120, %rsp		# a struct sysinfo: 112 bytes
	movq	%rsp, %rdi
	movl	$99, %eax		# sysinfo
	syscall
	testq	%rax, %rax
	jnz	2f
	movq	32(%rsp), %rax		# totalram
	addq	64(%rsp), %rax		# totalswap
	jc	1f
	movl	104(%rsp), %ecx		# mem_unit
	mulq	%rcx
	jc	1f
	movabsq	$0x4000000000000000, %rcx
	cmpq	%rcx, %rax
	jbe	3f
1:	movabsq	$0x4000000000000000, %rax
	jmp	3f
2:	xorl	%eax, %eax
3:	andq	$-4096, %rax
	addq	$120, %rsp
	ret

# __funk_rt_catch_overflow(): has SIGSEGV run __funk_rt_overflow on a
# stack of its own, since a run that outgrew its stack has none left, and
# unblocks SIGSEGV, which a parent can leave blocked across execve.
__funk_rt_catch_overflow:
	leaq	.Lalt_stack(%rip), %rdi
	xorl	%esi, %esi
	movl	$131, %eax		# sigaltstack
	syscall
	movl	$11, %edi		# SIGSEGV
	leaq	.Lsig_overflow(%rip), %rsi
	xorl	%edx, %edx
	movl	$8, %r10d		# the size of a signal set
	movl	$13, %eax		# rt_sigaction
	syscall
	movl	$1, %edi		# SIG_UNBLOCK
	leaq	.Lsig_segv(%rip), %rsi
	xorl	%edx, %edx
	movl	$8, %r10d
	movl	$14, %eax		# rt_sigprocmask
	syscall
	ret

# __funk_rt_overflow(signal, info, context): the SIGSEGV handler. Every
# access to the stack is at most a page below one made before it
# (docs/decisions/x86-64-backend.md#stack-probes), so a run that outgrows
# its stack faults first in the guard page. That fault is reported in one
# line, with exit status 2; the buffered output is never written, so
# standard output stays empty, but for what the C library wrote out before
# the fault.
# Any other SIGSEGV is not the runtime's to report, and SA_RESETHAND has
# put the default action back. After any other fault the handler returns,
# so the instruction faults again and ends the process with the fault's own
# code and address, as with no handler. A SIGSEGV that a process sent, the
# handler sends again before it returns.
__funk_rt_overflow:
	cmpl	$0, 8(%rsi)		# si_code: above 0 for a fault, not
	jle	2f			# for a signal that a process sent
	movq	16(%rsi), %rax		# si_addr, the address of the fault
	subq	__funk_rt_guard(%rip), %rax
	cmpq	$4096, %rax
	jae	1f
	subq	$8, %rsp
	call	__funk_rt_err_program
	movq	__funk_rt_function(%rip), %rdi
	call	__funk_rt_err_text
	leaq	.Lmsg_ran_out(%rip), %rdi
	call	__funk_rt_err_cstr
	movq	__funk_rt_stack(%rip), %rdi
	call	__funk_rt_err_num
	leaq	.Lmsg_stack_reserved(%rip), %rdi
	jmp	.Ldie
1:	ret
2:	movl	$39, %eax		# getpid
	syscall
	movl	%eax, %edi
	movl	$11, %esi		# SIGSEGV
	movl	$62, %eax		# kill
	syscall
	ret

# __funk_rt_restore(): where a signal handler returns to.
__funk_rt_restore:
	movl	$15, %eax		# rt_sigreturn
	syscall
	ud2

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

# __funk_rt_flush(): writes the buffer to standard output. With the C
# library, its streams go first; when they cannot be written, the program
# exits with 2, as on any failed write.
__funk_rt_flush:
.ifdef .Lfunk_libc
	subq	$8, %rsp
	xorl	%edi, %edi
	call	fflush
	addq	$8, %rsp
	testl	%eax, %eax
	jz	1f
	movl	$2, %edi
	jmp	__funk_rt_exit
1:
.endif
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
	call	__funk_rt_err_text
	leaq	.Lmsg_colon(%rip), %rdi
	addq	$8, %rsp
	jmp	__funk_rt_err_cstr

# __funk_rt_err_text(cstr): writes a NUL-terminated string from the command
# line to standard error, each control byte (below 0x20, or 0x7f) as \xHH,
# so that the message stays on one line. Runs of other bytes are written
# whole.
__funk_rt_err_text:
	pushq	%rbx
	pushq	%r12
	subq	$24, %rsp
	movq	%rdi, %rbx		# the start of the run
	xorl	%r12d, %r12d		# the length of the run
1:	movzbl	(%rbx,%r12), %eax
	testl	%eax, %eax
	jz	3f
	cmpl	$0x20, %eax
	jb	2f
	cmpl	$0x7f, %eax
	je	2f
	incq	%r12
	jmp	1b
2:	movq	%rbx, %rsi
	movq	%r12, %rdx
	movl	$2, %edi
	call	__funk_rt_write
	movzbl	(%rbx,%r12), %eax
	leaq	.Lhex(%rip), %rdx
	movb	$92, (%rsp)		# '\'
	movb	$120, 1(%rsp)		# 'x'
	movl	%eax, %ecx
	shrl	$4, %ecx
	movzbl	(%rdx,%rcx), %ecx
	movb	%cl, 2(%rsp)
	andl	$15, %eax
	movzbl	(%rdx,%rax), %eax
	movb	%al, 3(%rsp)
	movq	%rsp, %rsi
	movl	$4, %edx
	movl	$2, %edi
	call	__funk_rt_write
	leaq	1(%rbx,%r12), %rbx
	xorl	%r12d, %r12d
	jmp	1b
3:	movq	%rbx, %rsi
	movq	%r12, %rdx
	movl	$2, %edi
	call	__funk_rt_write
	addq	$24, %rsp
	popq	%r12
	popq	%rbx
	ret

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
	subq	$56, %rsp
	movq	%rdi, %rsi		# n, sign-extended to 128 bits
	sarq	$63, %rsi
	leaq	48(%rsp), %rdx
	call	__funk_rt_format
	movq	%rax, %rsi
	leaq	48(%rsp), %rdx
	subq	%rax, %rdx
	movl	$2, %edi
	call	__funk_rt_write
	addq	$56, %rsp
	ret

	.section	.rodata
	.p2align	3
.Lsig_ignore:	.quad	1, 0, 0, 0	# struct sigaction: SIG_IGN, no flags
# struct sigaction: the handler, SA_SIGINFO | SA_ONSTACK | SA_RESETHAND
# | SA_RESTORER, the restorer, and no signal blocked
.Lsig_overflow:	.quad	__funk_rt_overflow, 0x8c000004, __funk_rt_restore, 0
# stack_t: the signal handler's stack, no flags, and its size
.Lalt_stack:	.quad	__funk_rt_alt_stack, 0, 65536
.Lsig_segv:	.quad	1 << 10		# a signal set that holds SIGSEGV
.Lhex:	.ascii	"0123456789abcdef"
.Lopen:	.ascii	"{\"values\":["
.Lopen_end:
.Lclose:	.ascii	"]}\n"
.Lclose_end:
.Lprogram_default:	.asciz	"program"
.Lmsg_usage:	.asciz	"usage: "
.Lmsg_usage_args:	.asciz	" @FUNCTION ARG...\n"
.Lmsg_colon:	.asciz	": "
.Lmsg_no_function:	.asciz	"no function "
.Lmsg_in_program:	.asciz	" in this program\n"
.Lmsg_takes:	.asciz	" takes "
.Lmsg_arguments_not:	.asciz	" arguments, not "
.Lmsg_no_stack:	.asciz	"cannot reserve "
.Lmsg_stack_for:	.asciz	" bytes of stack for "
.Lmsg_ran_out:	.asciz	" ran out of the "
.Lmsg_stack_reserved:	.asciz	" bytes of stack reserved for it\n"
.Lmsg_newline:	.asciz	"\n"

	.bss
	.p2align	4
__funk_rt_out_buf:	.skip	4096
__funk_rt_out_len:	.skip	8
__funk_rt_count:	.skip	8
__funk_rt_program:	.skip	8
__funk_rt_args:	.skip	8
__funk_rt_guard:	.skip	8	# the guard page below the run's stack
__funk_rt_stack:	.skip	8	# the bytes of the run's stack
__funk_rt_function:	.skip	8	# the function's name, as typed
	.p2align	4
__funk_rt_alt_stack:	.skip	65536	# the stack of the SIGSEGV handler
