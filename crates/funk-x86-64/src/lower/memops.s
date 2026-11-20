# funk's own memcpy, memmove and memset (#234). The backend appends this
# file, once, to the assembly of a module in which a function copies, moves
# or sets memory, so the module's object file carries the routines and a
# program that only does that links with no C library (ADR-2026-11-09-1551;
# docs/decisions/x86-64-backend-lowering-memory.md#copies-moves-and-sets).
#
# Every symbol is local to the object file, with no .globl, and starts with
# __funk_rt_, which no fir function's symbol does (ADR-2026-10-30-1232). So
# a module that also links the host's C library never clashes with its
# memcpy, memmove or memset. Each routine is a System V function of three
# arguments that returns nothing: the destination in %rdi, the source, or
# the byte to set in %sil, in %rsi, and the length in bytes in %rdx. It uses
# only %rax, %rcx, %rsi and %rdi, which System V lets a callee clobber, and
# 8 bytes of stack below the caller's %rsp: its return address. The
# direction flag is clear on entry, as System V asks, and on return.
#
# A length of 0 touches no memory, whatever the pointers are: a rep string
# instruction with %rcx = 0 does nothing (#234, Q1 B).

	.text

# __funk_rt_memcpy(d, s, n): copies n bytes from s to d, first to last. The
# two ranges are equal or disjoint, since a partial overlap is UB (#234,
# Q2 B), so each byte copied is one that the source held before the copy.
	.type	__funk_rt_memcpy, @function
	.p2align	4
__funk_rt_memcpy:
	movq	%rdx, %rcx
	rep movsb
	ret
	.size	__funk_rt_memcpy, .-__funk_rt_memcpy

# __funk_rt_memmove(d, s, n): copies n bytes from s to d as the source held
# them before the move began, however the ranges overlap. d - s, read as
# unsigned, is below n when d is in [s, s + n): a copy first to last would
# then overwrite source bytes before it reads them, so it copies last to
# first, with the direction flag set. Otherwise it copies first to last.
	.type	__funk_rt_memmove, @function
	.p2align	4
__funk_rt_memmove:
	movq	%rdx, %rcx
	movq	%rdi, %rax
	subq	%rsi, %rax
	cmpq	%rdx, %rax
	jb	.Lrt_mem_backward
	rep movsb
	ret
.Lrt_mem_backward:
	# n > 0 here, since d - s < n.
	leaq	-1(%rsi,%rdx), %rsi
	leaq	-1(%rdi,%rdx), %rdi
	std
	rep movsb
	cld
	ret
	.size	__funk_rt_memmove, .-__funk_rt_memmove

# __funk_rt_memset(d, v, n): writes the byte v, the low byte of %rsi, into
# each of the n bytes from d.
	.type	__funk_rt_memset, @function
	.p2align	4
__funk_rt_memset:
	movl	%esi, %eax
	movq	%rdx, %rcx
	rep stosb
	ret
	.size	__funk_rt_memset, .-__funk_rt_memset
