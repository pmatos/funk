# Current decisions: semantics, the M1 design

This page continues semantics.md. It says what the ADRs decide about the meaning
of fir in M1. It is the record: when this page and an ADR disagree, the page
wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610).

These are decided designs, and the spec and the tools do not implement them
yet. `ptr` has values but no ops yet (ADR-2026-11-09-1542). M0 has no
global data (ADR-2026-11-09-1546). `funk` and `fir-ref` are fixed to the core
dialect (ADR-2026-11-09-1545). Each M1 feature goes through every layer
(ADR-2026-11-09-1548). semantics.md says what holds in the spec and the tools
today. process.md says what M1 covers. semantics-m1-trace.md says what a run
shows and how the world answers it, and semantics-m1-dialects.md says how
dialects, levels and the second dialect work in M1.

## Memory

A pointer is an allocation id and an offset. Memory maps each allocation to an
array of abstract units. Each unit is concrete bits, poison or a fragment of a
pointer. Fresh memory holds poison (ADR-2026-11-09-1542).

An access is immediate UB in each of these cases (ADR-2026-11-09-1542):

- it is out of bounds;
- its allocation is freed;
- its pointer has no provenance for that allocation.

`ptr.expose` turns a pointer into an integer and marks its allocation exposed.
`ptr.from_int` turns an integer back into a pointer, with the provenance of an
exposed allocation that contains the address. No other op converts between
pointers and integers. Optimizations may assume that distinct allocations do
not alias, unless a pointer was exposed and rebuilt from an integer
(ADR-2026-11-09-1542).

The human ruled this memory model on 2026-11-09, on #206. Rejected: flat,
concrete memory, where pointers are integers. Every allocation's address would
become a choice, which explodes exhaustive runs and blocks most alias
reasoning. Rejected too: logical blocks with no integer casts in M1, so C and
kernel code that casts pointers could not be lowered in M1.

A pointer type names its memory. The core `ptr` is `ptr<0>`, and other memories
are `ptr<N>`. A dialect may add memories of its own. A pointer moves between
memories only through an op that a dialect provides (ADR-2026-11-09-1542). The
spec and the tools have the pointer types: a value of `ptr<N>` is poison or a
pointer, refined only by itself. Every module has memory 0, so `ptr` is valid,
and `ptr<N>` for `N ≥ 1` waits for the data layout to declare memory `N`
(#231).

The module's data layout gives each memory its unit of addressing and its
pointer width. The unit is an 8-bit byte unless the layout says otherwise. Sizes
and offsets in a memory count its units (ADR-2026-11-09-1542).

Only exposed allocations have integer addresses. `fir-ref` assigns them from one
canonical layout: in allocation order, aligned and deterministic. That is one of
the address assignments the spec allows, so exhaustive mode stays finite.
`fir-ref` covers one assignment, not all of them. A test whose observations
depend on an exposed address is interpreter-only, and the harness never compares
raw addresses (ADR-2026-11-09-1542).

Memory ops carry an `ordering` attribute. M1 accepts only `nonatomic`, so a
concurrency model (S6) needs no format change. Allocations carry a kind: stack,
global, or heap through external calls. Managed memory can be added as another
kind later (ADR-2026-11-09-1542). The world may create and free heap
allocations when it answers an external call (ADR-2026-11-09-1540).

Every theorem that relies on `ptr` having no values is restated
(ADR-2026-11-09-1542). Stage 3a of #231 restates call congruence for a callee
with no pointer parameter, and #214 proves it for the rest.

An op allocates in a memory for the current call. The allocation is freed when
the call returns. Heap allocation stays a call to an external function such as
`malloc`, with no op of its own (ADR-2026-11-09-1548).

A `volatile` attribute on loads and stores makes the access an event of the
trace. The access cannot be removed, duplicated or reordered with other events
(ADR-2026-11-09-1548).

## The memories of a run

The spec gives one memory of this model, for a unit of any width, in
`lean/Fir/Memory/`, with its accesses and their laws. No op or type uses
memory yet (#231). Memory is a state layer over the way of computing
(ADR-2026-11-10-2350):

- `Memories Mem unit`, in `lean/Fir/Memory/Frames.lean`, holds one memory for
  each memory name, with a unit width per name that the data layout will give,
  and a stack of frames. A frame lists the stack allocations its call made.
- `MonadMemory` gives allocating, freeing, loading and storing on a named
  memory, and a faulting access is UB. `StateT (Memories Mem unit) m` keeps
  `m`'s choice and UB and gives the memory effect. A stuck path keeps the
  memories it reached, and a UB path shows none. Monad morphisms lift through
  the layer.
- `MonadFrame.frame`, in `lean/Fir/Execution/Frame.lean`, runs a computation as
  one call. `Func.runOps` runs each callee in a frame, and `Func.run` runs the
  function it starts with in one, so no op runs outside a frame. In the layer a
  frame enters a call, runs it, then frees the frame's allocations. In the set
  monad and the tree of choices a frame is the computation itself.
- A dialect whose ops touch no memory runs in the layer by lifting its rules,
  and its runs with memory are its runs (`Func.memRuns_eq`). Ops that touch
  memory state their semantics in a monad with `MonadMemory`. Progress, fuel
  monotonicity and refinement for them are proved over the layer, and
  `fir-ref` walks the layer over the tree of choices (#231).
- Runs with memory start from empty memories. Until #233 builds what a run
  shows, an observer of a run with memory sees its returned values only.
- A proper tail call replaces its caller's frame, so the caller's stack
  allocations are freed before the callee runs. The tail-call ticket adds a
  second frame operation that leaves the current frame and enters a fresh one
  in its place.

Rejected: thread memory through the interpreter, as fuel is. Every op's
semantics, every dialect and every proof about op semantics would change, for
ops that never touch memory. Rejected too: free a call's stack allocations by
marking each memory's allocation count at the call. The interpreter would have
to enumerate memory names, which may be infinite.

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
assembly block, a volatile store of the pointer or `ptr.expose` hands it out.

The human ruled globals on 2026-11-09, on #209. Rejected: typed globals that
hold a fir value, which would tie globals to the shape of aggregates while a C
frontend lays out bytes anyway. Rejected too: every global exported, which is
wrong for C's `static`.

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
on every memory that can have escaped to them. Passes may rely on a
declaration because of its proof, and each new op costs one soundness proof per
effect it leaves out (ADR-2026-11-09-1541).

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
  alike. So a copied pointer keeps its provenance. Overlapping source and
  destination is UB.
- Move does the same and allows overlap.
- Set writes one unit value into each unit. The value is sized to the memory's
  unit: an `i8` on the default memory, whose unit is an 8-bit byte unless the
  layout says otherwise, and an integer of the unit's width on any other.

Copy and move read the source memory and write the destination. Set writes. All
three may be UB, for out-of-bounds access. A frontend lowers a C call to
`memcpy` to the copy op, not to an external call. The naive backend lowers them
to funk's own runtime routines `memcpy`, `memmove` and `memset`, not the C
library's, so a program that only copies, moves or sets memory keeps the
static link without the C library (ADR-2026-11-09-1551).

The human ruled these ops on 2026-11-09, on #220. On 2026-11-11 the human ruled
on #251 that set writes one unit value, not a byte, and on #274 that funk's
runtime carries its own routines, in place of the C library's that #220 named;
#234 builds them. Rejected: calls to external functions with known meanings,
which lose provenance and make every copy an event.

## Aggregates

In M1 aggregates are layouts over memory, not values (ADR-2026-11-09-1550).

A layout is a size, an alignment and a list of fields. Each field is an offset
and a scalar type: an integer, a float or a pointer. An array is a repeated
field. Sizes and offsets count the units of the memory the layout describes.

One op computes the address of a field or element from a pointer and a layout.
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
memory that can have escaped to it, so its key covers all of them
(ADR-2026-11-09-1552).

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
