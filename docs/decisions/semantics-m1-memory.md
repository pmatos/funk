# Current decisions: semantics, M1 memory

This page continues semantics-m1-design.md with the memory of M1: the memory
model, its pointers, the ops that touch it, the memories of a run and the
core's guarantees with memory. It is the record: when this page and an ADR
disagree, the page wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610).

## Memory

A pointer is an allocation id and an offset. Memory maps each allocation to an
array of abstract units. Each unit is concrete bits, poison or a fragment of a
pointer. Fresh memory holds poison (ADR-2026-11-09-1542).

An access is immediate UB in each of these cases (ADR-2026-11-09-1542):

- it is out of bounds;
- its allocation is freed;
- its pointer has no provenance for that allocation;
- it is misaligned (the human's ruling of 2026-11-11 on #231, Q4; see
  [Aligned accesses](#aligned-accesses)).

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
pointer, refined only by itself. Every module has memory 0, so `ptr` is valid
in every module, and `ptr<N>` for `N ≥ 1` is valid when the module's data
layout declares memory `N` (ADR-2026-11-12-1821).

A pointer moves by `ptradd`: `%q: ptr = ptradd %p, %k` takes a `ptr<N>` and
an `iW` of any width, and gives a `ptr<N>` with the same provenance, whose
offset is `%p`'s plus `%k` read as signed, in units of the memory `N`. The
offset never wraps and may leave the allocation; only an access through it
must be in bounds. A poison operand gives poison, it is never UB, and its
effect set is empty. It has no attributes, and any other shape does not
decode (ADR-2026-11-13-0251; `lean/Fir/Core/Pointer.lean`). The backend
lowers it in stage 5 of #231. A native address wraps at the pointer's width
where the offset does not; the two agree on every access the spec allows,
and `ptr.expose` (#232) settles which address an offset outside the
pointer's width exposes. Rejected: UB or poison for a result out of its
allocation, as LLVM's `inbounds` gives beyond one past the end, since code
that moves a pointer out of its allocation and back is common.

The module's data layout gives each memory its unit of addressing and its
pointer width. The unit is an 8-bit byte unless the layout says otherwise. Sizes
and offsets in a memory count its units (ADR-2026-11-09-1542). It also gives
each memory its byte order, `little` alone in M1, its pointers' alignment and
whether it is non-integral; [text-format-layout.md](text-format-layout.md)
says what holds for it (ADR-2026-11-12-1821). A run gives each memory its entry,
and an op takes the unit width, byte order and pointer width of the memory it
accesses from that memory's entry, never from the dialect or the op
(ADR-2026-11-13-0906; [semantics-effects.md](semantics-effects.md#soundness)).

A value takes whole units of the memory it is stored in, placed in the
memory's byte order (ADR-2026-11-12-2125). An `iN` takes `ceil(N / U)` units
of `U` bits: a store sets the bits past `N` to zero, and a load ignores them,
so an `i1` loaded from `0xFF` is 1. A `ptr<N>` takes `ceil(P / U)` units,
each a fragment of the pointer with the memory number `N`, where `P` is
memory `N`'s pointer width. Poison takes as many poison units. A load gives
poison from a poison unit, an integer load from a pointer's fragments, and
a `ptr<N>` load from anything but one pointer's fragments of memory `N` in
order, so an integer copy of memory carries no pointer. The encoding laws
take the byte order as a parameter and hold at every order
(`lean/Fir/Memory/EncodeLaws.lean`). The human ruled odd widths, punned
loads and the byte-order parameter on 2026-11-11, on #231. Rejected: reject
widths that are not a multiple of the unit, so `i1` and `i20` could never be
stored; and immediate UB for a punned load, which makes copying memory as
integers UB.

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
(ADR-2026-11-09-1542). Stage 3a of #231 restated call congruence for a callee
with no pointer parameter, and #214 proved it for every callee
(`semantics-refinement.md#congruence-in-the-callee`).

An op allocates in a memory for the current call. The allocation is freed when
the call returns. Heap allocation stays a call to an external function such as
`malloc`, with no op of its own (ADR-2026-11-09-1548).

## Stack allocation

`alloca` allocates room for a constant count of values of a type, written
`%p: ptr = alloca stack i32 4` and `%p: ptr(1) = alloca stack i8 12 align(4)`
(ADR-2026-11-14-0915; `lean/Fir/Core/Alloca.lean`). The human ruled on
2026-11-14, on #378, that the op takes a type and a constant count, that its
default alignment is the type's natural alignment, and that the natural
alignment of `iN` is the least power of two that is at least its units:
`i8` 1, `i24` 4, `i32` 4, `i64` 8 and `i128` 16 in memory 0
(`MemLayout.intAlign`). Rejected by that ruling: a count of units, with no
type to give a default alignment; a run-time count in M1 (#381); and
capping the natural alignment at the pointer's.

- The attributes are the kind, the type, the count when it is not 1 and
  `align(A)` when given, separated by spaces as every op's are. The human
  confirmed the spaces on 2026-11-14 (#382). Rejected: commas, as #378's
  examples wrote them, a second attribute grammar for one op.
- The op allocates the count times the units of the type in the memory of
  its result, with its kind and alignment. The pointer has provenance for
  the allocation at offset 0, and its units are poison. The frame of the
  call frees a stack allocation when the call returns.
- Validation accepts the kind `stack` alone, a count of at least 1, a power
  of two for `A` no larger than `MemLayout.limit` (`MemLayout.ValidAlign`,
  the layout's own rule) and a valid integer type.
  `global` and `heap` decode, as hooks in the format (ADR-2026-11-09-1542).
- The element is an integer type until float and pointer loads and stores
  land, as the human ruled on 2026-11-14 (#382). Rejected: float and pointer
  elements now, with no access to read or write them.
- `A` is at most `MemLayout.limit`, 2^24 - 1, the bound of the data layout's
  own alignments, so the largest `A` is 2^23; the count has no bound. An
  allocation larger than a machine holds is a resource error at run time, as
  a deep recursion is, and not a rule of the spec. The human ruled both on
  2026-11-14 (#382). Rejected: a bound on the count, which would not keep an
  allocation within a machine, since one `i16777215` takes 2 MiB. `fir-ref`
  has no resource error of its own: it holds each allocation's units, so a
  huge one exhausts its memory. `funk build` does not lower `alloca` yet.
  The bound covers a written `A` only. The natural alignment that an op
  without `align(A)` takes is not bounded: in a memory with 1-bit units, an
  element wider than 2^23 bits has the natural alignment 2^24, as a layout
  line's pointers of such a width do. Whether validation should bound it too
  waits on the human (#385).
- The G0 check reads the words of `AllocaText.lean` and `TypeText.lean` as
  core words, but leaves out `align` by name (`SHARED_WORDS` in
  `scripts/check_g0.py`), since the data layout's generic grammar writes it
  too. The human ruled this on 2026-11-14 (#382). Rejected: reading only
  `Text.lean` and `TypeText.lean`, which checks no `alloca` word.
- It is never UB, its result is never poison, and its effect set is
  "allocates in memory `N`". It has no rule in the set monad, so the core
  dialect no longer meets the lawful class there; its obligations with
  memory are proved op by op, and `alloca`'s by its own rule
  (`lean/Fir/Core/AllocaLaws.lean`). A core function that reaches no
  `alloca` reaches no memory (`Core.reachesNoMemory`). The semantics with
  memory carries the core's guarantees (below).

A `volatile` attribute on loads and stores makes the access an event of the
trace. The access cannot be removed, duplicated or reordered with other events
(ADR-2026-11-09-1548).

## Aligned accesses

An op's load or store carries an alignment, in units: its promise that the
access's address is a multiple of it. A misaligned access is immediate UB (the
human's ruling of 2026-11-11 on #231, Q4). A block has no address, only the
alignment it was allocated with, which every address it may be given is a
multiple of. The human ruled on 2026-11-14 (#388, option A) that an access
aligned to `A`, through a pointer at offset `o` into a block aligned to `B`, is
aligned exactly when `A` divides `B` and `o`, so that it is aligned at every
address the block may have. This is LLVM's rule. An access aligned to 1 is
always aligned. An `i32` access aligned to 4 into `alloca stack i8 16` is
therefore UB, even at offset 0, unless the `alloca` says `align(4)`
(`Memory.aligned`, `Memory.loadAligned` and `Memory.storeAligned` in
`lean/Fir/Memory/Model.lean`, their laws in `AlignLaws.lean`).

- An aligned access faults as the plain one does first, with no provenance,
  freed or out of bounds, and only then as misaligned. The fault decides only
  the reason a run gives for its UB.
- The memory effect's `load` and `store` take the access's alignment, and the
  state layer makes each an aligned access, so a rule can only load or store
  with an alignment. Whether an access is aligned depends on the allocations,
  not on any unit, so a store still does not read its memory.
- In the state layer a load writes, allocates and frees nothing, reads only
  its own memory, has one outcome and is monotone; a store writes only its own
  memory, allocates nothing, reads no memory, its own included, has one
  outcome and is monotone (`lean/Fir/Execution/MemoryLoadLaws.lean`,
  `MemoryStoreLaws.lean`). Encoding and decoding keep refinement
  (`lean/Fir/Memory/EncodeLaws.lean`). The core's `load` and `store` (stages
  4e-2 and 4e-3 of #231) meet their obligations from these.

Rejected by the human's ruling of 2026-11-14 on #388: aligned at some
address, misaligned only when no address of the block could make the access
aligned (option B). No pass or backend could then rely on an `align` promise.
Rejected too: checking an access against the address that `fir-ref`'s
canonical layout gives, which the spec does not fix and which only exposed
allocations have.

## The memories of a run

The spec gives one memory of this model, for a unit of any width, in
`lean/Fir/Memory/`, with its accesses and their laws. `alloca` is the one
op that uses memory yet (#231). Memory is a state layer over the way of computing
(ADR-2026-11-10-2350):

- `Memories Mem unit`, in `lean/Fir/Memory/Frames.lean`, holds one memory for
  each memory name, with a unit width per name, and a stack of frames. The
  semantics with memory takes each memory's layout entry and gives the
  memories the units of their entries (`unitsOf lay`). A frame lists the
  stack allocations its call made.
- `MonadMemory` gives allocating, freeing, loading and storing on a named
  memory, each load and store with its alignment, and a faulting access,
  misaligned included, is UB. An allocation records its kind and
  its alignment in units, which refinement and the effect obligations
  compare.
  `StateT (Memories Mem unit) m` keeps `m`'s choice and UB and gives the
  memory effect. A stuck path keeps the memories it reached, and a UB path
  shows none. Monad morphisms lift through the layer.
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

## The core's guarantees

The semantics with memory carries the guarantees for the whole core
dialect, `alloca` included. The statements without memory cover only the
code that touches none: those over the set monad cover the ops other than
`alloca`, and those that ask a function to reach no memory cover such
functions. The human ruled this on 2026-11-14, on #384 (option A).
Rejected: splitting out a memory-free core dialect, whose old statements
would hold with no condition, with the memory ops beside it (option C),
which changes the dialect's structure where the versions with memory
already cover every op.

These hold for every core op, and for every function of a valid core
module, `alloca` included:

- the lawful classes with memory: `Core.lawfulDialectTotal`,
  `Core.lawfulDialectMonotone` and `Core.lawfulDialectMemPoison`
  (`lean/Fir/Core/MemoryRuns.lean`), and the class of its effects,
  `LawfulDialectEffects`, proved by `Core.lawfulDialectEffects`, from which
  its instance is built;
- progress, `Core.progress`, and no stuck path, `Core.neverStuck`;
- refined arguments, `Core.args_isRefinedBy`, which also holds for an
  invalid module;
- congruence in the callee from given memories,
  `Core.replaceBody_isRefinedBy_of_from` and
  `Core.caller_isRefinedBy_of_from`, with no condition on the callee
  (#214; `lean/Fir/Core/MemoryCallRefine.lean`).

Each new memory op, starting with stage 4e's `load` and `store`, keeps every
one of them holding, with its own rule with memory and its own proofs, as
`alloca` does (`lean/Fir/Core/AllocaLaws.lean`, joined to the tied ops by
`Core.Op.memCases`).

PR #382 narrowed these statements, which now cover memory-free code; beside
each is what covers the whole core:

- `Core.lawfulDialectPoison`, the lawful class in the set monad, went:
  `alloca` has no rule there. The three classes with memory replace it; in
  a dialect that lifts the set monad they hold exactly when it does
  (`LawfulDialectPoison.iff_mem`). So `Func.progress_of_lawful`,
  `Func.runs_args_isRefinedBy_of_lawful` and
  `Func.runs_replaceBody_isRefinedBy_of_lawful` no longer apply to the
  core: `Core.progress`, `Core.args_isRefinedBy` and
  `Core.replaceBody_isRefinedBy_of_from` do. The tests `coreToy_lawful`,
  `coreToyBit_lawful` and `coreProbe_lawful` went with it; their instances
  of the classes with memory stay (`lean/FirTest/Deps.lean`,
  `lean/FirTest/LawfulRefine.lean`).
- `Core.Op.total` and `Core.Op.total_all` ask that the op touch no memory:
  `Core.lawfulDialectTotal` covers every op, `alloca` by
  `Core.alloca_memTotal`.
- `Core.Op.returnsOnDefined_valid` asks it too:
  `Core.lawfulDialectMemPoison` covers every valid op.
- `Core.replaceBody_isRefinedBy` and `Core.caller_isRefinedBy` ask that
  `@g` reach no memory (`Core.reachesNoMemory`), which held of every
  function before #382: `Core.replaceBody_isRefinedBy_of_from` and
  `Core.caller_isRefinedBy_of_from` ask nothing of it.
- `Core.Op.liftsSetM`, `Core.Op.effects_touchesNoMemory` and
  `Core.reachesNoMemory` are about touching no memory, so no version covers
  a memory op: it has no tie and declares a memory effect. The obligations
  they served hold through `Core.Op.memCases` and
  `Core.lawfulDialectEffects`.
- `Core.memDenoteIn_mapsDenote` still covers every op, and asks the
  morphism to keep allocation, which `MonadMorphism.state_alloc` gives for
  the state layer.

`Core.Op.liftsSetM_of_terminator` and `Core.tyAttr_bare` keep their
statements: the first has a new proof, and the second moved within
`lean/Fir/Core/Names.lean`.
