# Current decisions: semantics, the M1 design

This page continues semantics.md. It says what the ADRs decide about the
meaning of fir in M1. It summarizes the ADRs it cites and does not replace
them. When this page and an ADR disagree, the page is wrong
(ADR-2026-11-09-1610).

These are decided designs, and the spec and the tools do not implement them
yet. M0 gives `ptr` no values and no ops (ADR-2026-11-09-1542). M0 has no
global data (ADR-2026-11-09-1546). A module holds functions only and declares
no dialects (ADR-2026-11-09-1543). `funk` and `fir-ref` are fixed to the core
dialect (ADR-2026-11-09-1545). Each M1 feature goes through every layer
(ADR-2026-11-09-1548). semantics.md says what holds in the spec and the tools
today. process.md says what M1 covers.

## What a run shows

A run shows an ordered trace of events (ADR-2026-11-09-1540). The core dialect
has two kinds of event:

- An external call: the callee's symbol, its arguments, and the units reachable
  from its pointer arguments when the call is made.
- A volatile access: load or store, the accessed location as the observer sees
  it, and the value read or written.

The trace ends in one of three ways:

- a return, with the returned values and the contents of the memory reachable
  from globals and from returned pointers;
- UB;
- divergence.

Two ends of a run match when some one-to-one renaming of allocations makes
their reachable memory equal. Raw addresses are never compared. Memory that no
observer can reach stays invisible, so a store to it can be removed.

Another dialect may add events of its own, such as a device's I/O, since
observations already come from the dialect (ADR-2026-11-09-1540).

## The world and refinement

A callee that funk did not compile answers from the world. For each call, the
world gives its results and may write into memory that has escaped to it.
Behaviour is stated for a given world. The world is not the environment of
values in which a run looks names up (ADR-2026-11-09-1540).

A target refines a source when it does so for every world. For each world,
every trace the target shows is one the source shows, with poison refined as
today. UB in the source allows only a target that first shows the source's
events before the UB (ADR-2026-11-09-1540).

Every refinement theorem gains a quantifier over worlds. The first theorems to
be restated are those that #206 and #209 touch.

Each test supplies a scripted world: the results of each external call, in
order, and any writes into escaped memory. A test that calls an external
function must come with its script. `fir-ref run` reports the trace and the end
of the run (ADR-2026-11-09-1540).

For a native run, the harness generates a stub library from the same script. It
is linked in place of the external functions. It records each call (symbol,
arguments, reachable bytes) and replays the scripted results. A wrapper that the
harness generates dumps the reachable memory at return. The one judgement module
compares the two sides (ADR-2026-11-06-1218, ADR-2026-11-09-1540).

## Memory

A pointer is an allocation id and an offset. Memory maps each allocation to an
array of abstract units. Each unit is concrete bits, poison or a fragment of a
pointer. Fresh memory holds poison (ADR-2026-11-09-1542).

An access is immediate UB in each of these cases (ADR-2026-11-09-1542):

- it is out of bounds;
- its allocation is freed;
- its pointer has no provenance for that allocation.

The spec now gives one memory of this model, for a unit of any width, in
`lean/Fir/Memory/`, with its accesses and their laws. No op, type or run
uses it yet (#231).

`ptr.expose` turns a pointer into an integer and marks its allocation exposed.
`ptr.from_int` turns an integer back into a pointer, with the provenance of an
exposed allocation that contains the address. No other op converts between
pointers and integers. Optimizations may assume that distinct allocations do
not alias, unless a pointer was exposed and rebuilt from an integer
(ADR-2026-11-09-1542).

A pointer type names its memory. The core `ptr` is `ptr<0>`, and other memories
are `ptr<N>`. A dialect may add memories of its own. A pointer moves between
memories only through an op that a dialect provides (ADR-2026-11-09-1542).

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
kind later (ADR-2026-11-09-1542).

Every theorem that relies on `ptr` having no values is restated. Call congruence
is the first, in #214 (ADR-2026-11-09-1542).

An op allocates in a memory for the current call. The allocation is freed when
the call returns. Heap allocation stays a call to an external function such as
`malloc`, with no op of its own (ADR-2026-11-09-1548).

A `volatile` attribute on loads and stores makes the access an event of the
trace. The access cannot be removed, duplicated or reordered with other events
(ADR-2026-11-09-1548).

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
as an assembler does (ADR-2026-11-09-1546).

An `export` global is visible to code that funk did not compile, and is
reachable memory for an observer. Weak, common and visibility linkage wait for
the C frontend, M4 (ADR-2026-11-09-1546).

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
bits. Frontends set the markers to match the C ABI. Markers are not required on
every narrow parameter (ADR-2026-11-09-1547).

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
implementation, a new ADR revises them (ADR-2026-11-09-1553).

## Effects

Each op declares a set of effects drawn from this list (ADR-2026-11-09-1541):

- reads memory `m`;
- writes memory `m`;
- allocates or frees in memory `m`;
- may-UB;
- may produce poison: a poison result on operands with no poison, beside the
  op's poison class (ADR-2026-11-09-2249);
- observable: it adds an event to the trace;
- control: it is a terminator.

The empty set is pure. Reads, writes, allocation and freeing name the memory
they touch. Effects on different memories commute. An external call, an indirect
call to an unknown function and inline assembly without a narrower declaration
carry every effect on every memory that can have escaped to them
(ADR-2026-11-09-1541).

A dialect declares the effects of its own ops, including effects on memories it
adds. A new Lean class, beside `DialectPoison`, gives each op's effect set, and
`OpSpec` gives it in Rust. The Rust registry's declarations are checked against
the Lean ones, as op signatures are. `DialectPoison` folds into the effect class
when the class lands (ADR-2026-11-09-1541). The class has landed in Lean;
semantics-effects.md says what holds today.

For each op, the spec proves that its declaration over-approximates its
semantics. An op that does not declare a write to `m` leaves `m` unchanged. One
without may-UB never ends in UB. One without observable adds no event. The same
goes for each effect. Passes may rely on a declaration because of that proof.
Each new op costs one soundness proof per effect it leaves out
(ADR-2026-11-09-1541).

Every core op of M0 is pure, may produce poison or may-UB, as its rules already
say. `call` carries its callee's summary (semantics-effects.md,
ADR-2026-11-10-2108). Each M1 op is classified when it
lands, in its own ticket, by the same rule (ADR-2026-11-09-1541):

- Loads read and may-UB.
- Stores write and may-UB.
- Stack allocation allocates.
- Memory intrinsics read and write.
- Volatile accesses are also observable.
- External calls and inline assembly are observable.
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
- Set writes one byte value into each unit.

Copy and move read the source memory and write the destination. Set writes. All
three may be UB, for out-of-bounds access. The naive backend lowers them to
calls to the C library's `memcpy`, `memmove` and `memset`. A frontend lowers a C
call to `memcpy` to the copy op, not to an external call (ADR-2026-11-09-1551).

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

## Floating point

Floating point is one type family, `float<e,m>`, with `e` exponent bits and `m`
explicit mantissa bits. The usual names are aliases: `f16`, `bf16`, `f32`, `f64`
and `f128`. The spec and `fir-ref` handle every IEEE-shaped format. A format
that is not IEEE-shaped, such as fp8 e4m3fn, is left to dialects
(ADR-2026-11-09-1549).

The semantics is strict IEEE 754. Denormals are honoured. Flush-to-zero is an
explicit target attribute. When an op's IEEE result is a NaN, fir chooses any
NaN bit pattern of the format, so payload and sign are nondeterministic. #219
decides how `fir-ref` and the harness handle that choice (ADR-2026-11-09-1549).

Every rounding op carries `round = rne`. Round to nearest even is the only value
M1 accepts (ADR-2026-11-09-1549).

The fast-math flags are (ADR-2026-11-09-1549):

- `nnan`: a NaN operand or result makes the result poison.
- `ninf`: an infinite operand or result makes the result poison.
- `nsz`: the sign of a zero result is a free choice.
- `contract` and `reassoc` are reserved words that the verifier rejects. They
  are permissions for passes, not meanings of an op, and M2's optimizer decides
  them.

The spec defines fir's float ops on Lean's model, with a layer that adds the NaN
choice. It defines the conversions between widths itself. Facts it needs are
proved here, or checked with `decide` and `bv_decide`. Before relying on the
model, the implementation confirms that each operation works for a format other
than binary32 and binary64 (ADR-2026-11-09-1549).

The naive backend lowers `f32` and `f64` with SSE in M1, and reports any other
format as a diagnostic. A native result in a format it does not lower is judged
by `fir-ref` alone (ADR-2026-11-09-1549).

## Inline assembly

Inline assembly is an op tagged with its target. It holds a template,
constraints, operands, results, clobbers and an explicit effect set, observable
or not. A module for another target rejects it (ADR-2026-11-09-1552).

Running an assembly block is an event of the trace. The world answers it with
its results and with writes into memory that its declared effects allow.
`fir-ref` takes the answer from the test's script, as for external calls
(ADR-2026-11-09-1552).

M1 brings the spec, the parser, printer and verifier on both sides, and
`fir-ref`. Until M4, the naive backend rejects inline assembly with a diagnostic,
and native runs of such code wait. The C frontend brings constraint handling
(ADR-2026-11-09-1552).

## Dialects

Every dialect other than the core writes its ops, types and attributes as
`name.word`. Core words stay bare. A module's dialects combine as a sum routed
by the prefix, for ops, types and attributes alike. The sum moves from
`lean/FirTest/` into the spec. Test dialects keep the `toy.` prefix
(ADR-2026-11-09-1543). The sum is in the spec now, and semantics-dialects.md
says what holds of it.

A dialect declares the dialects it depends on, and may name their types. That is
how an extension op takes a core value (ADR-2026-11-09-1543).

A dialect registers kinds of item through the one grammar, as it registers ops.
So a new kind needs no parser change. The core registers `func`, `global`,
external declarations and `module`. A `module` item holds a nested symbol table,
so nested and device modules exist, in #211 (ADR-2026-11-09-1543).

Each module declares the dialects it uses. The verifier rejects any op, type,
attribute or kind of item from a dialect outside the set. A nested module
declares its own set, which is how a host module holds a device module. A module
that declares none uses the core alone, so M0's texts stay valid
(ADR-2026-11-09-1543).

The format and the dialect classes admit region kinds other than the core's CFG
region, such as unordered dataflow regions. No other kind is built in M1.
Effects and observations come from the dialect too. The round-trip and
validation proofs are restated over sums of dialects and over registered kinds
of item (ADR-2026-11-09-1543).

## Levels and lowering

In v0 a module holds ops of one abstraction level, and lowering takes a whole
module from one level to the next. Levels mix only through nested modules: a
host module at one level may hold a device module at another
(ADR-2026-11-09-1544).

A lowering that funk performs, from one dialect set to another, must produce a
module that refines its input. It is proved once in Lean, or checked per compile
once S8 exists (ADR-2026-11-09-1544).

A dialect is not required to lower to core. A terminal dialect is lowered only
by its own backend, to its own hardware. Its programs are still checked by its
semantics in `fir-ref`. Its backend is checked against `fir-ref` like the x86-64
backend, by refinement of observed runs (ADR-2026-11-09-1544).

## The second dialect

The second dialect in tree is shaped like a GPU kernel language
(ADR-2026-11-09-1545):

- A host module holds a nested device module whose dialect set includes the GPU
  dialect. Kernel functions live in the device module.
- It adds ops of its own, such as work-item and work-group ids and sizes, and at
  least one type or attribute of its own.
- It adds a memory in a non-default address space, such as work-group shared
  memory, with effects named by that memory.

`fir-ref` runs one work-item of a kernel, with its ids given as inputs. Ops whose
meaning needs other work-items, such as barriers, are left out or admitted
without execution rules (ADR-2026-10-30-1855). A launch op in host code is out
of M1. M1's results are not a model of a whole kernel. The semantics grows into
a full kernel model only when S6 decides concurrency (ADR-2026-11-09-1545).

The dialect is terminal. It has no lowering to core and no native backend in M1
(ADR-2026-11-09-1544, ADR-2026-11-09-1545).

The G0 checks show these things with it (ADR-2026-11-09-1545):

- Generic code in `funk-ir` and `lean/Fir` loads it with no change but its
  registration.
- A host module with a device module round-trips byte for byte across Rust and
  Lean, and both sides validate it the same way, must-reject cases included.
- Its kernels run in `fir-ref` one work-item at a time, and `funk` and `fir-ref`
  agree on its corpus.
- The generic results (round trip, refinement, congruence) are restated for a
  dialect set that includes it.

Use-once (linear) values stay covered by the toy test of #167. A quantum-style
dialect remains a candidate for a later G0 check. The implementation of this
dialect, in #212, waits for memory and for nested modules
(ADR-2026-11-09-1545).
