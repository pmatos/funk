# Current decisions: semantics, the M1 design

This page continues semantics.md. It says what the ADRs decide about the meaning
of fir in M1. It is the record: when this page and an ADR disagree, the page
wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610).

These are decided designs, and the spec and the tools implement only some of
them yet: `ptr` has values (ADR-2026-11-09-1542), and its ops so far are
`ptradd` (ADR-2026-11-13-0251), `alloca` (ADR-2026-11-14-0915), `load`
and `store` (ADR-2026-11-14-2316), and `memcpy` and `memmove`
(ADR-2026-11-18-2131). M0 has no
global data (ADR-2026-11-09-1546). `funk`, `fir-ref fmt`, `fir-ref
validate` and `fir-ref run` read the core and the second dialect, `gpu`
(ADR-2026-11-09-1545; semantics-m1-dialects.md). Each M1 feature goes through every layer
(ADR-2026-11-09-1548). semantics.md says what holds in the spec and the tools
today. process.md says what M1 covers. semantics-m1-trace.md says what a run
shows and how the world answers it, and semantics-m1-dialects.md says how
dialects, levels and the second dialect work in M1.

## Memory

[semantics-m1-memory.md](semantics-m1-memory.md) says what holds for M1's
memory: the memory model, its pointers and their ops, stack allocation, and
the memories of a run.

## Globals

A global is an item with (ADR-2026-11-09-1546):

- a symbol;
- the memory it lives in, the default memory when none is given;
- a size in that memory's units, and an alignment;
- an initializer of constant units, which may include the address of a symbol
  plus an offset, such as `@f` or `@g + 8`;
- a `const` flag, and writing a constant global is UB;
- a linkage, `internal` (the default) or `export`.

Each global is one allocation of kind global, live for the whole run. An op gets
its address by symbol. A frontend writes initial data as units and relocations,
as an assembler does. A global in a GPU memory names that memory
(ADR-2026-11-09-1546).

An `export` global is visible to code that funk did not compile, and an
observer sees it. Weak, common and visibility linkage wait for the C frontend,
M4 (ADR-2026-11-09-1546). An `internal` global is observable only once its
address escapes (ADR-2026-11-09-1540): an external call, an observable inline
assembly block, one that gets it as a pointer operand and may write escaped
memory (ADR-2026-11-09-1541), a volatile store of the pointer or `ptr.expose`
hands it out.

The human ruled globals on 2026-11-09, on #209. Rejected: typed globals that
hold a fir value, which would tie globals to the shape of aggregates while a C
frontend lays out bytes anyway. Rejected too: every global exported, which is
wrong for C's `static`.

A global is an item of the core's kind `global` (ADR-2026-11-19-0124):
`global @msg() size(8) align(1) const units(104, 105, 0) {` and `}`, with
`memory(N)` first when `N` is not 0, the words `const` and `export` in
that order, and the initializer's pieces `units(U, ...)`, `zeros(N)`,
`addr(@s)` and `addr(@s, K)`, which fill the units in order. An address
takes the units of one pointer of `@s`'s memory. A valid global names a
declared memory and a power-of-two alignment, gives units that fit its
memory's unit, takes addresses of globals of its own table only, and has
an initializer no larger than its size. The spec, `fir-ref fmt` and
`validate`, and `funk-ir` read, print and check globals; they have no run
meaning yet, and the backend leaves them out, until #237's later stages.
The words `global` and `const` are ADR-2026-11-09-1546's: the human ruled
on 2026-11-20 (#237 Q4) that a global keeps them, and that the G0 check, on
the Lean and the Rust side, lists both with `align` among the words generic
code shares with the core, since the core's text writes them too
(`alloca`'s kind `global`, the op `const`). Rejected: `data` and
`constant`, which stage 1 shipped so that no check changed, but which are
not what the ADR and its readers call a global. A global's allocation keeps
the kind `global`; a function's address is an allocation of kind `function`
(the human's ruling of 2026-11-19 on #235), so `addr(@f)` waits until runs
make those. Rejected:
units and relocations at explicit offsets, two parts that must agree.

## External declarations

An external declaration gives a symbol and a signature, and no body. A call to
it is an observable event (ADR-2026-11-09-1547).

Its signature may end in `...`. A call to it then passes extra arguments after
the fixed ones. Defining a variadic fir function stays out of M1
(ADR-2026-11-09-1547, ADR-2026-11-09-1548).

An integer parameter or result narrower than 32 bits may carry `sext` or `zext`.
That holds in a declaration and in a function's own signature
(ADR-2026-11-09-1547):

- A marked parameter is extended by the caller, and the callee may rely on it.
- A marked result is extended by the callee, and the caller may rely on it.
- With no marker, nothing is guaranteed, and neither side may rely on the upper
  bits.

The verifier rejects a marker on a type that is not an integer narrower than 32
bits. Frontends set the markers to match the C ABI (ADR-2026-11-09-1547). The
human ruled this on 2026-11-09, on #209, and on 2026-11-11, on #251, that an
unmarked `i1` promises nothing either
([x86-64-backend-abi.md](x86-64-backend-abi.md#the-unmarked-i1-result)). Rejected: markers
required on every narrow parameter, noisy for every caller that is not C.

## Calls and terminators

An op gives a pointer to a function from its symbol. A call through a pointer
states the callee's signature. Calling through a pointer whose target has
another signature is UB (ADR-2026-11-09-1548).

`unreachable` is a terminator that is immediate UB when reached
(ADR-2026-11-09-1548).

A proper tail call is an explicit terminator, `tail_call @f args`, with an
indirect form. It ends a block, calls the callee and returns the callee's
results as the caller's own. Only marked calls are proper. A `call` followed by
`ret` is promised nothing (ADR-2026-11-09-1553).

The verifier rejects a tail call unless all of these hold
(ADR-2026-11-09-1553):

- The callee's result types equal the caller's.
- No stack allocation of the caller is passed to the callee or reachable from
  its arguments.
- The target's calling convention lets the callee reuse the caller's frame.
  Under System V on x86-64, the callee's stack arguments must fit in the
  caller's incoming stack-argument area.

The spec gives each run a frame depth, its first measure of space. Frame depth
is the number of calls that have not returned. A tail call replaces the caller's
frame instead of adding one, so a chain of tail calls keeps the depth of its
first caller. `fir-ref` and every backend keep this promise. A native run checks
it with deep tail recursion in the corpus. A tail call's effects are those of a
call, plus control. If the conditions or the promise meet a blocker in
implementation, ADR-2026-11-09-1553 and this page are edited in place.

The human placed proper tail calls (#100) in M1 as an explicit marker on
2026-11-09, on #204, accepted this design the same day, and confirmed it on
2026-11-11, on #100. Rejected: every call in tail position is proper, as in
Scheme. Some cannot reuse the frame under System V, so the promise would fail
silently or force an expensive convention on every call.

## Effects

Each op declares a set of effects, and the spec proves the declaration sound
(ADR-2026-11-09-1541). semantics-effects.md says what holds. Effects on
different memories commute. An external call, an indirect call to an unknown
function and inline assembly without a narrower declaration carry every effect
on every memory that can have escaped to them. Such a block may also read and
write the allocation that a pointer operand points into and every allocation
reachable from it through stored pointers. If a block may write escaped memory,
as such a block may, its pointer operands escape when it runs. The human ruled
on 2026-11-15 (#309, #240). Passes may rely on a declaration because of its
proof, and each new op costs one soundness proof per effect it leaves out
(ADR-2026-11-09-1541).

Every core op of M0 is pure, may produce poison or may-UB, as its rules already
say. `call` carries its callee's summary (semantics-effects.md,
ADR-2026-11-09-1541). Each M1 op is classified when it
lands, in its own ticket, by the same rule (ADR-2026-11-09-1541):

- Loads read and may-UB.
- Stores write and may-UB.
- Stack allocation allocates.
- Memory intrinsics read and write.
- Volatile accesses are also observable.
- External calls are observable. Inline assembly is observable only when its
  effect set says so (ADR-2026-11-09-1552).
- `unreachable` and tail calls are control.

The aegraph stays an optimizer view outside the spec. may-UB is the hook that
will cover `assume` (ADR-2026-11-09-1541).

## Memory intrinsics

Three ops copy, move and set memory, over one memory and a length in its units
(ADR-2026-11-09-1551):

- Copy carries each unit across exactly: bits, poison and pointer fragments
  alike. So a copied pointer keeps its provenance. Its source and
  destination must be equal or disjoint: a partial overlap is UB.
- Move does the same and allows overlap.
- A length of 0 is a no-op, whatever the pointers are, a dangling, null or
  poison one included.
- Set writes one unit value into each unit. The value is sized to the memory's
  unit: an `i8` on the default memory, whose unit is an 8-bit byte unless the
  layout says otherwise, and an integer of the unit's width on any other.

Copy and move read the source memory and write the destination. Set writes. All
three may be UB, for out-of-bounds access, unless the length is 0. A frontend lowers a C call to
`memcpy` to the copy op, not to an external call. The naive backend lowers them
to funk's own runtime routines `memcpy`, `memmove` and `memset`, not the C
library's, so a program that only copies, moves or sets memory keeps the
static link without the C library (ADR-2026-11-09-1551).

The human ruled these ops on 2026-11-09, on #220. On 2026-11-11 the human ruled
on #251 that set writes one unit value, not a byte, and on #274 that funk's
runtime carries its own routines, in place of the C library's that #220 named;
#234 builds them. On 2026-11-18 the human ruled on #234 that a length of 0 is
a no-op whatever the pointers are (Q1 B), and that a copy onto its own range
is allowed, only a partial overlap being UB (Q2 B), both as in LLVM.
Rejected: calls to external functions with known meanings, which lose
provenance and make every copy an event; a zero length that is an access, as
in C17, which makes the zero-length copies of Rust and C2y frontends UB; and
any shared unit UB, as in C, which would forbid lowering `*a = *b` to the
copy op.

Copy and move are written `memcpy ORDERING %d, %s, %n` and
`memmove ORDERING %d, %s, %n`, destination, source and length in C's order,
with no result (ADR-2026-11-18-2131). Both pointers are of one memory, the
length is a run-time integer of any width, read as unsigned, that counts the
memory's units, and the ordering is always written, `nonatomic` alone valid.
There is no `align(A)` in M1: each access is aligned to one unit. With a
length other than 0, a poison pointer is UB, as for a load. A poison length
runs as some length, chosen as `freeze` chooses bits, so it is UB wherever
some length is, and the op stays in the `propagates` class
(ADR-2026-10-29-2006). Rejected: a poison length always UB, as in LLVM's
LangRef, which the `propagates` class forbids, since with an `i1` length over
a one-unit allocation no length is UB; it would need the class `exception`.
This paragraph records agent work, not a ruling, and the poison length waits
for the human's ruling on #234.

The spec has both ops, `Core.Op.memCopy` with a `CopyKind`
(`lean/Fir/Core/MemCopy.lean`), through every layer but native code (stage 2
of #234); `memset` is stage 3, and native code and funk's runtime routines
stage 4. The rule takes the length first: 0 does nothing; otherwise a poison
pointer is UB, then a `memcpy` whose ranges partly overlap, then the copy of
units of stage 1 (`lean/Fir/Execution/MemoryCopyLaws.lean`): a load of the
units through the source, then a store of them through the destination, so
a move whose ranges overlap writes what the source held before it began.
Every law of the op comes from the copy of units, through the laws of a
choice in the state layer (`lean/Fir/Execution/MemoryChoiceLaws.lean`), and
joins the core's guarantees through `Core.Op.memCases`, whose statements
gain no hypothesis.

## Aggregates

In M1 aggregates are layouts over memory, not values (ADR-2026-11-09-1550).

A layout is a size, an alignment and a list of fields. Each field is an offset
and a scalar type: an integer, a float or a pointer. An array is a repeated
field. Sizes and offsets count the units of the memory the layout describes.

A layout is an item of the core's kind `aggregate` (ADR-2026-11-16-1546):
`aggregate @pair() memory(0) size(16) align(8) field(0, i64) field(8, ptr) {`
and `}`, with `field(O, T, C)` for a repeated field of `C` elements. A field
takes the units of its type in the layout's memory, aligned as `alloca` aligns
it; a repeated field's elements are rounded up to that alignment, so four `i24`
in memory 0 take 16 units. A valid layout names a declared memory and a
power-of-two alignment, and places each field of an integer, float or pointer
type at a multiple of its alignment, no larger than the layout's, within the
size and apart from every other field. A float takes the units of its bits at
the natural alignment of its size, as #264 gives them (#236). The human ruled on 2026-11-16, on #236: repeated elements
are rounded up to their alignment (Q2 B); the run passes the module's layouts
to every op's rule (Q1 A); and an element index out of range behaves as
`ptradd` (Q3 A).
Rejected: elements spaced by the type's units alone, which misaligns arrays of
`i24` and C's `long double`.

One op computes the address of a field or element from a pointer and a layout:
`fieldaddr` (ADR-2026-11-18-2041), as in `%q: ptr = fieldaddr @pair 1 %p` and
`%e: ptr = fieldaddr @row 0 %p, %k`. It names the layout of its own table and a
field by its number, and moves the pointer by the field's offset plus the
index, read as signed, times the element's step. Like `ptradd` it keeps the
pointer's provenance, is never UB and gives poison only for a poison operand;
an index out of the field's elements is an address, and only an access through
it must be in bounds. Validation requires the layout to be in the pointer's
memory, the field to exist, and an index only on a repeated field. The rule
holds for every record of items the run may give, with no hypothesis: one
without the layout or field moves the pointer by 0. Rejected: the offset and
type written at each use, two parts that must agree with the layout.
Data moves through the scalar loads and stores. No op makes an aggregate value,
or extracts from or inserts into one. Each unit of an aggregate in memory may be
poison, so nothing extra is needed for poison (ADR-2026-11-09-1550).

A parameter may be `byval<layout>` and a result `sret<layout>`, in a function's
own signature and in an external declaration. The x86-64 backend classifies them
by the System V rules from the layout's fields. A variadic call may pass a
`byval` aggregate (ADR-2026-11-09-1550).

Dialects may add value types such as vectors and tensors. First-class aggregate
values in the core may be added later if a frontend needs them
(ADR-2026-11-09-1550).

The human ruled this on 2026-11-09, on #210. Rejected: first-class aggregate
values with extract and insert ops, as in LLVM, which would bring per-field
poison rules and register lowering of large values into M1 as a second way to
do what memory and multiple results already do.

## Floating point

Floating point is one type family, `float<e,m>`, over every IEEE-shaped format,
with strict IEEE 754 semantics and nondeterministic NaN bits
(ADR-2026-11-09-1549). semantics-floats.md says what the ADRs decide and what
holds today.

## Inline assembly

Inline assembly is an op tagged with its target. It holds a template,
constraints, operands, results, clobbers and an explicit effect set, observable
or not. A module for another target rejects it (ADR-2026-11-09-1552).

The effect set decides whether a block is an event (ADR-2026-11-09-1552):

- With observable, running the block is an event of the trace, as GCC's
  `asm volatile` is.
- Without observable, the block adds no event. Passes may delete, merge or move
  it within its declared reads and writes, as with GCC's plain `asm`. They may
  merge or move it only when no write to the memories it reads comes between,
  a write by the block itself included.

The world answers a block with its results and with writes into memory that its
declared effects allow. `fir-ref` takes the answer from the test's script, as
for external calls. The answer for a block without observable is keyed by the
block, its operands and the contents of the memories it declares it reads, not
by its position in the trace. A block with no narrower declaration reads every
memory that can have escaped to it, and the allocation that a pointer operand
points into with every allocation reachable from it through stored pointers, so
its key covers all of them (ADR-2026-11-09-1552, ADR-2026-11-09-1541).

M1 brings the spec, the parser, printer and verifier on both sides, and
`fir-ref`. Until M4, the naive backend rejects inline assembly with a diagnostic,
and native runs of such code wait. The C frontend brings constraint handling.
It maps C's `asm` to a block without observable, and `asm volatile` to one with
it (ADR-2026-11-09-1552).

The human ruled inline assembly on 2026-11-09, on #220. On 2026-11-11 the human
ruled on #251 that the effect set decides whether a block is an event, and on
#299 that an unobservable block's answer depends on the memory it reads.
Rejected: the backend emits it in M1, which would pull GCC constraint handling
into the IR milestone. Rejected too: every block is an event, so passes could
never remove a block that only computes; and keying an unobservable block by
the block and its operands alone, which forces a block that reads changing
memory to be marked observable.
