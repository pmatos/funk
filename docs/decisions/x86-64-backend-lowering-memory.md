# Current decisions: the x86-64 backend, lowering memory

This page continues [x86-64-backend-lowering.md](x86-64-backend-lowering.md).
It says what holds today for how the backend lowers pointers and the memory
ops of #231, `ptradd`, `alloca`, `load` and `store`, the field address of
#236, `fieldaddr`, the copies, moves and sets of #234, `memcpy`,
`memmove` and `memset`, the ops of #232 that turn pointers into
integers and back, `ptr_expose` and `ptr_from_int`, and the globals of
#237 with their address, `globaladdr`. It is the record: when
this page and an ADR disagree, the page wins, and the ADR is fixed or deleted
(ADR-2026-11-09-1610). The ops' meaning is on
[semantics-m1-memory.md](semantics-m1-memory.md),
[semantics-m1-stack.md](semantics-m1-stack.md) and
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
significant first. Every such memory shares the process's address space, and
allocations never overlap, so the addresses that native code gives each
memory's allocations are one address policy of the spec for that memory. A
pointer that `ptr_from_int` rebuilds in a memory from any address, another
memory's included, may reach under that policy only an exposed allocation
of its own memory that holds the address, its end included, whose bytes
native code reaches too; through any other, every access is UB
([Pointers as integers](#pointers-as-integers)). No other op turns a
pointer of one memory into a pointer of another. A value of a pointer of any
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

## Field addresses

`fieldaddr @s i %p` adds the offset of the field `i` of the layout `@s` to
the address, with one `leaq`, or a `movabsq` and an `addq` for an offset
past 32 bits, and nothing for offset 0. With an index, `fieldaddr @s i %p,
%k` first adds the index, read as signed as `ptradd`'s offset is and the low
half of an `i128`, times the field's stride: the units of one value of its
type rounded up to its alignment (the human's ruling of 2026-11-16 on #236,
Q2 B), one `imulq` by an immediate, since a type of at most `2^24 - 1` bits
takes at most 2^21 bytes, and none for a stride of 1. The backend places
each layout's fields once per module; the layout is the first of the
module's own table with that symbol, the one validation checked the op
against. Its memory is
the pointer's, so its units are bytes, or the pointer is reported where it
is defined, as the human ruled on 2026-11-15 (#399) for every memory of
wider units. The field's type is no value of the op, so a field of a type
the backend does not lower, such as `i24`, still has its address computed
(`lower/field_addr.rs`).

The address wraps at 64 bits where the spec's offset does not, as for
`ptradd`; the two agree on every access the spec allows. An index outside
the field's elements gives an address and no fault, as the spec gives one
(Q3 A). The differential harness checks struct and array programs against
`fir-ref` (`tests/fir/canonical/fieldaddr-programs.fir`). Rejected: a
`leaq` with a scaled index for strides of 1, 2, 4 or 8 bytes, a second
lowering beside the one that serves every stride, for a naive backend
whose speed is not measured on the code it emits.

## Pointers as integers

`ptr_expose` and `ptr_from_int` are moves: each copies its operand's slot
into its result's through `%rax`, since a pointer is its address
(`lower/ptr_int.rs`). The data layout asks that the integer be as wide as
the memory's pointers, so it is an `i64`; a pointer of any other memory is
reported where it is defined. This is the lowering that #232 asks for.

It agrees with the spec because native code's addresses are one address
policy of each memory ([semantics-m1-addresses.md](semantics-m1-addresses.md)):
an allocation's address is a multiple of its alignment, from 1, below
`2^64 - 1`, and overlaps no live allocation, while a freed stack slot may
hold a live allocation by the time a dangling pointer to it is exposed, as
the human ruled on 2026-11-20 (#232, question C). The integer `ptr_expose`
gives is then an address that the spec may give, and a pointer that
`ptr_from_int` rebuilds from an address in a live, exposed allocation of
its memory, its end included, reaches what the allocation that the spec's resolver may pick holds. From
any other address it rebuilds a pointer through which every access is UB,
so whatever native code then reads refines the spec.

`fir-ref` follows the canonical layout, which native code need not, so a
differential test returns only what an address reaches, the difference of
two addresses of one allocation, or what every policy agrees on, such as
an address modulo its allocation's alignment
(`tests/fir/canonical/ptr-int-programs.fir`). A test whose canonical run is
UB where another policy or resolver has none stays interpreter-only, as the
human ruled on 2026-11-20 (#451); the harness already counts a differential
test with UB among its outcomes as invalid, so no new check is needed.
Rejected: masking or checking the integer at run time, which the spec does
not ask for.

## Globals

Each global of the module's own table is a symbol of the object file,
spelled as a function's is (`abi::symbol`), after the code and the runtime
helpers (`lower/globals.rs`, #237 stage 3). A `const` global goes to
`.rodata`, so a store to it faults, which the spec makes UB (#237 Q2); a
writable global whose initializer gives only zero units to `.bss`; any
other to `.data`. Each is aligned with `.balign` to its alignment, marked
`.type @object` with its `.size`, and is `.globl` when it is `export`, a
local symbol otherwise. Its initializer's units are bytes, an `addr(@g, K)`
piece is the relocation `.quad g+K`, whose addend wraps at 64 bits as
`ptradd`'s offset does, and the units past the initializer are zeros, as
the human ruled on 2026-11-20 (#237 Q1). Each process runs one function,
so each run starts with the initial units. The executable is not
position-independent, so the relocations are resolved when it links. A
module with globals also defines the hidden table `__funk_globals`, which
lists each placed global for the runtime's `--memory` report
([x86-64-backend-executable.md](x86-64-backend-executable.md#reporting-memory)).

`%p: ptr<N> = globaladdr @g` is `leaq g(%rip), %rax` and a store to the
result's slot. Validation makes `@g` a global of the op's own table and of
memory `N`, and the backend reports the result unless it realises memory
`N`, so every global that an op names is placed. A nested module's globals
are left out with its functions, which `funk build` does not build, and a
run holds its own table's globals only (#237 Q3).

A global of a memory that the backend does not realise, of wider units or
32-bit pointers, is reported at the global, and so is one with an `addr`
piece to a global of such a memory: the backend places no unit that it
cannot write as bytes. `leaq` and calls relative to `%rip` assume the small
code model, in which code and data lie within 2 GiB, so the globals, each
with the padding of its alignment, take at most 2^30 bytes, and each global
past that is reported. Native code's addresses for globals are one address
policy of the spec, as for every allocation, so a differential test
returns what a global's address reaches, never the address
(`tests/fir/canonical/globals-programs.fir`, `globaladdr.fir`). This is the
agent's design for #237 stage 3, not a ruling. The stage plan names memory
0; every memory of 8-bit units and 64-bit pointers is placed, since the
backend realises each such memory as it realises memory 0, as the human
ruled on 2026-11-15 (#399). Rejected: `.data.rel.ro` for a constant global
with relocations, which only a position-independent executable needs; and
leaving out a global that no op names, which would drop an `export`
global's symbol.

## Loads and stores

`load` and `store` move the value's units with one move, or two for an
`i128`: one byte for `i1` and `i8`, two for `i16`, four for `i32`, eight for
`i64` and a pointer, sixteen for `i128`, its low half at the lower address. A
load zero-extends what it reads into `%rax`. A store of an `i1` writes its byte
as 0 or 1, the zero padding of the human's ruling of 2026-11-11 (#231, Q2),
since the bits of a value above its width are unspecified
([x86-64-backend.md](x86-64-backend.md#values-and-widths)). A load of an `i1`
reads its byte, and its bits above bit 0 are such bits.

An `alloca` of floats takes the bytes and the natural alignment of the
integer of their width, `1 + e + m` bits. A load or a store of an `f32` or
`f64` moves its 4 or 8 bytes through `%xmm0` with `movss` or `movsd`, which
copy the bits as they are, so a NaN keeps its sign and payload and a
signalling NaN stays signalling
([semantics-m1-memory-access.md](semantics-m1-memory-access.md#floats-in-memory),
#264). The value goes to or from its slot as other float ops' do: `movq`
from `%xmm0` into the slot, whose bits above an `f32`'s 32 are unspecified,
and `movss` or `movsd` from it. A float of any other format is reported
where it is defined, as at every other float op
([x86-64-backend-lowering-floats.md](x86-64-backend-lowering-floats.md)).
Rejected: moving a float's bits through `%rax` with integer moves, which
gives the same bytes but not the SSE moves that #264 asks for.

`align(A)` and the ordering need no code. x86-64 accesses any address, a
misaligned access is UB in the spec (the human's ruling of 2026-11-14 on
#388), and M1's one ordering is `nonatomic`. A punned load, which the spec
makes poison, reads the bytes that are there. Each access loads the address
into `%rcx` and the value through `%rax`, and `%rdx` for an `i128`, or
through `%xmm0` for a float.

## Copies, moves and sets

`memcpy`, `memmove` and `memset` each call funk's own routine,
`__funk_rt_memcpy`, `__funk_rt_memmove` or `__funk_rt_memset`, of the runtime
helper `lower/memops.s`, which the module's object file carries once when a
function calls one, as the `i128` division routines are carried
([x86-64-backend-lowering.md](x86-64-backend-lowering.md#division-at-i128)).
This is the human's ruling of 2026-11-11 on #274, in ADR-2026-11-09-1551: a
program that only copies, moves or sets memory links static, with no C
library. The routines are local symbols with the `__funk_rt_` prefix, which
no fir function's symbol has, so a module that also links glibc
([x86-64-backend.md](x86-64-backend.md#linking-with-the-host-c-library)) keeps
glibc's `memcpy`, `memmove` and `memset` apart from funk's
(`crates/funk-x86-64/tests/memops.rs`).

Each is a System V function of the destination in `%rdi`, the source, or the
`i8` value of `memset`, in `%rsi`, and the length in bytes in `%rdx`. Each
uses only `%rax`, `%rcx`, `%rsi` and `%rdi` and its return address, and
copies or fills with one `rep movsb` or `rep stosb`, which with a length of 0
touches nothing, whatever the pointers (#234, Q1 B). `memcpy` copies first to
last, exact for ranges that are equal or disjoint, the only ones it allows
(Q2 B). `memmove` copies last to first, with the direction flag set and then
cleared, when the destination starts inside the source, and first to last
otherwise, so it writes what the source held before it began. A
destination equal to the source starts inside it when the length is above
0, so that copy too runs last to first with the direction flag set: slow
but correct, and left for a performance milestone, with no ticket filed
(the human's ruling of 2026-11-20).

The length is read as unsigned: zero-extended from its width, and an `i128`
whose high half is not zero saturates to `2^64 - 1`, as an `alloca` count
does, since no allocation the backend makes holds 2^64 bytes and such a length
is UB: the routine runs until it faults, rather than copy the length's low half
and return. A poison length is the bits its slot holds, one of the lengths the spec
chooses from (the human's ruling of 2026-11-19 on #234), and a poison value
writes the byte its slot holds, which refines poison units. A pointer of a
memory of wider units is reported where it is defined, as for every op, so
none of the three is lowered in such a memory. The differential harness
checks the three against `fir-ref` (`tests/fir/canonical/memops-native.fir`).
Rejected: calls of the C library's routines, which the ruling of #274
replaced; global `memcpy`, `memmove` and `memset` symbols, which clash with
glibc's; and inline `rep` code at each op, which the ruling's routines
replace.

## Stack allocation

Each run of an `alloca` makes an allocation that lives until its call
returns, so an `alloca` in a loop makes a new one on every pass
([semantics-m1-stack.md](semantics-m1-stack.md#stack-allocation)). The
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
