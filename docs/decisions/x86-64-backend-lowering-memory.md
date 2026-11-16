# Current decisions: the x86-64 backend, lowering memory

This page continues [x86-64-backend-lowering.md](x86-64-backend-lowering.md).
It says what holds today for how the backend lowers pointers and the memory
ops of #231: `ptradd`, `alloca`, `load` and `store`. It is the record: when
this page and an ADR disagree, the page wins, and the ADR is fixed or deleted
(ADR-2026-11-09-1610). The ops' meaning is on
[semantics-m1-memory.md](semantics-m1-memory.md) and
[semantics-m1-memory-access.md](semantics-m1-memory-access.md).

## Pointers

A value of `ptr<N>` is a 64-bit address in one slot or register, of System V
class INTEGER, as a C pointer is. It passes to and from a function, through
block arguments, `select`, `freeze` and `poison`, as an `i64` does. `poison`
of a pointer writes the address 0.

The backend realises a memory whose data layout entry has 8-bit units and
64-bit pointers, in little-endian order: memory 0 by default, and any other
memory that the layout declares so. A unit is then a byte, an offset in units
is an offset in bytes, and the units of a value are its bytes, least
significant first. Every such memory shares the process's address space: no
op turns a pointer of one memory into a pointer of another, and allocations
never overlap, so no run can tell them apart. A value of a pointer of any
other memory, of 16-bit units or 32-bit pointers, is reported as unsupported
where it is defined, so no op of that memory is lowered and no access to it
is miscompiled (`lower/memory.rs`, `realised`).

#231 asks for the default memory; realising every memory of bytes is as the
human ruled on 2026-11-15 (#399). Rejected: realising only memory 0, which
would report a memory that x86-64 holds just as it holds memory 0; and
realising a memory of wider units by scaling its offsets, which nothing in M1
asks for, so such a memory is reported.

## Pointer offsets

`ptradd` adds its offset, read as signed, to the address: it sign-extends an
offset below 64 bits, so `true` at `i1` moves back one byte, and adds the low
half of an `i128`. The address wraps at 64 bits where the spec's offset does
not; the two agree on every access the spec allows, and an access the spec
does not allow is UB
([semantics-m1-memory.md](semantics-m1-memory.md#memory)).

## Loads and stores

`load` and `store` move the value's units with one move, or two for an
`i128`: one byte for `i1` and `i8`, two for `i16`, four for `i32`, eight for
`i64` and a pointer, sixteen for `i128`, its low half at the lower address. A
load zero-extends what it reads into `%rax`. A store of an `i1` writes its byte
as 0 or 1, the zero padding of the human's ruling of 2026-11-11 (#231, Q2),
since the bits of a value above its width are unspecified
([x86-64-backend.md](x86-64-backend.md#values-and-widths)). A load of an `i1`
reads its byte, and its bits above bit 0 are such bits.

`align(A)` and the ordering need no code. x86-64 accesses any address, a
misaligned access is UB in the spec (the human's ruling of 2026-11-14 on
#388), and M1's one ordering is `nonatomic`. A punned load, which the spec
makes poison, reads the bytes that are there. Each access loads the address
into `%rcx` and the value through `%rax`, and `%rdx` for an `i128`.

## Stack allocation

Each run of an `alloca` makes an allocation that lives until its call
returns, so an `alloca` in a loop makes a new one on every pass
([semantics-m1-memory.md](semantics-m1-memory.md#stack-allocation)). The
backend moves `%rsp` down at run time, below the frame: by the allocation's
bytes rounded up to 16, then down to its alignment, at least 16 so that
`%rsp` stays aligned for calls. The new `%rsp` is the pointer. The epilogue's
`leave` frees every allocation of the call. Nothing in a frame is addressed
from `%rsp`, so calls, their stack arguments and the result area work below
any number of allocations.

The allocation holds its count of values of its type: `ceil(N / 8)` bytes for
an `iN`, whatever width the backend lowers values at, and the bytes of `M`'s
pointer width for a `ptr<M>`. Without `align(A)` it takes the spec's default:
the least power of two at least those bytes, or, for a pointer in its own
memory, the alignment of that memory's pointers (the human's ruling of
2026-11-15 on #397). A count or size past 64 bits saturates, since no stack
holds it.

The move touches the page it starts on, then each page down to the new
`%rsp`, a page at a time, so every stack access stays at most a page below
one already made ([x86-64-backend.md](x86-64-backend.md#stack-probes)): an
alignment of 2^23 bytes cannot jump the guard page. An allocation past the
bottom of the address space aims at address 0, so its probes reach the guard
page first. The allocation's bytes are not cleared: they hold poison, which
any bits refine, so a load of fresh memory gives what the stack held. A
`poison` op writes zero for runs that reproduce
([x86-64-backend.md](x86-64-backend.md#poison)); fresh memory needs no such
rule, since no failure against `fir-ref` can come from a value that refines
poison.

An `alloca` in a block on no cycle of its function's branches runs at most
once per call. Its most, its rounded bytes and its alignment less 16, adds to
the function's stack need. An `alloca` on a cycle makes the need unbounded, as
a recursion does, so a run gets the process's stack limit and says when it
outgrows it, as the human ruled on 2026-11-15 (#399)
([x86-64-backend-executable.md](x86-64-backend-executable.md#the-figure)).

Rejected: a slot in the frame for each `alloca`, which one in a loop would
reuse on every pass, so that a pointer kept from an earlier pass would read
what a later pass stored, a miscompile; slots for the `alloca`s on no cycle and
moves for the rest, two lowerings where one serves both and costs a few
instructions; and reporting an `alloca` in a loop as unsupported, which the
spec allows and the corpus runs (`tests/fir/canonical/alloca.fir`, `@loop`).
