# Current decisions: semantics, M1 memory accesses

This page continues semantics-m1-memory.md with the accesses of M1's memory:
when an access is aligned, and the ops that load and store. It is the
record: when this page and an ADR disagree, the page wins, and the ADR is
fixed or deleted (ADR-2026-11-09-1610).

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

## Loads

`load` loads an integer through a pointer, written
`%v: i32 = load nonatomic %p` and `%v: i8 = load nonatomic align(2) %q`
(ADR-2026-11-14-2316; `lean/Fir/Core/Load.lean`). Its memory is its
pointer's.

- The attributes are the ordering, always written, then `align(A)` when
  given, separated by spaces. The orderings are LLVM's words, `nonatomic`,
  `unordered`, `monotonic`, `acquire`, `release`, `acq_rel` and `seq_cst`
  (`Memory.Ordering`). Every one decodes, and validation accepts `nonatomic`
  alone, so the others are hooks for a concurrency model
  (ADR-2026-11-09-1542). The words are an agent's proposal, put to the human
  on #391, which adds `load`; they have not ruled yet. Rejected: an ordering that may be left out, so
  a nonatomic load would have two spellings; and C++'s words, which have no
  `unordered`.
- `A` is valid as `alloca`'s is, a power of two no larger than
  `MemLayout.limit` (`MemLayout.ValidAlign`). With no `align(A)` the access
  is aligned to the natural alignment of `iW` in its memory
  (`MemLayout.intAlign`), as the human ruled on 2026-11-11 (#231, Q4).
- The result is an integer type until float and pointer loads land, as the
  human ruled on 2026-11-14 (#382, Q2): pointer loads come with pointer
  elements, in stage 4d-2b of #231.
- A poison pointer is immediate UB. Some defined pointer in its place, one
  with no provenance, faults, so this is UB by the op's own rules. Otherwise
  the op is the aligned load of the units of `iW`, its bits rounded up to
  whole units, and their decoding in the memory's byte order: units of bits
  give their number with the bits past `W` ignored, and a poison unit or a
  pointer's fragment gives poison, so fresh memory and a punned load give
  poison (the human's rulings of 2026-11-11 on #231). An access out of
  bounds, to a freed allocation, without provenance or misaligned is
  immediate UB.
- Its effects are "reads memory `N`", may-UB and may produce poison
  (`tests/dialects/effects.cases`). It has no rule in the set monad, and
  meets every obligation with memory by its own rule
  (`lean/Fir/Core/LoadLaws.lean`). The obligations reject a declaration of
  `load` without the read (`Core.Unlawful.loadNoRead_unlawful`, in
  `lean/Fir/Core/LoadReads.lean`).
- `fir-ref` runs it with the spec's own rule; `funk build` does not lower it
  yet (stage 5 of #231).

`Core.Op.memCases`, which splits an obligation of every core op into the
tied ops and the memory ops, gained a case for `load`, and
`Core.memDenoteIn_mapsDenote` asks the morphism to keep loads, which
`MonadMorphism.state_load` gives for the state layer. Every whole-core
guarantee keeps its statement (semantics-m1-memory.md#the-cores-guarantees).

## Stores

`store` stores an integer through a pointer and gives no result, written
`store nonatomic %v, %p` and `store nonatomic align(2) %b, %q`, the value
before the pointer (ADR-2026-11-14-2316; `lean/Fir/Core/Store.lean`). Its
memory is its pointer's.

- Its attributes, their validation and its default alignment are those of
  `load`, above: the same ordering words, `nonatomic` alone valid, and
  `align(A)` valid as `alloca`'s is (`Core.Op.Valid`; the shared Rust
  module `crates/funk-ir/src/dialects/core/access.rs`).
- The value is an integer type, as for `load` (the human's ruling of
  2026-11-14 on #382, Q2); pointer stores come with pointer elements, in
  stage 4d-2b of #231.
- A poison pointer is immediate UB, whatever the value, for the reason of
  `load`'s. Otherwise the op is the aligned store of the value's encoding
  in the memory's units and byte order (ADR-2026-11-12-2125): its bits
  rounded up to whole units, with the bits past `W` zero (the human's
  ruling of 2026-11-11 on #231, Q2), or as many poison units for a poison
  value. A store of poison is not UB: a load of those units gives poison
  again. An access out of bounds, to a freed allocation, without
  provenance or misaligned is immediate UB, and whether a store faults
  depends on how many units it writes, never on their values.
- A load of what a store wrote gives the value back. A narrower load gives
  the low units, in the byte order, and a wider one reads the units past
  the store as they were, poison in fresh memory: a different width is not
  a punned load, which reads a pointer's fragments as an integer or bits as
  a pointer (Q3).
- Its effects are "writes memory `N`" and may-UB
  (`tests/dialects/effects.cases`). It reads no memory, its own included,
  since whether it faults depends on the allocations and not on their units
  (`lean/Fir/Execution/MemoryStoreLaws.lean`), and it makes no poison, since
  it gives no result. Its poison class is `propagates`. It meets every
  obligation with memory by its own rule (`lean/Fir/Core/StoreLaws.lean`),
  and the obligations reject a declaration of `store` without the write
  (`Core.Unlawful.storeNoWrite_unlawful`, in
  `lean/Fir/Core/StoreWrites.lean`).
- `fir-ref` runs it with the spec's own rule; `funk build` does not lower it
  yet (stage 5 of #231).

`Core.Op.memCases` gained a case for `store`, and
`Core.memDenoteIn_mapsDenote` asks the morphism to keep stores, which
`MonadMorphism.state_store` gives for the state layer. Every whole-core
guarantee keeps its statement (semantics-m1-memory.md#the-cores-guarantees).
