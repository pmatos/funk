# Current decisions: semantics, dialects in M1

This page continues semantics-m1-design.md. It says what the ADRs decide about
dialects in M1: how levels and lowering work, and the second dialect in tree.
It is the record: when this page and an ADR disagree, the page wins, and the
ADR is fixed or deleted (ADR-2026-11-09-1610).

These are decided designs, and the spec and the tools do not implement them
all yet. semantics-dialects.md says what holds of dialects today.

## Dialects

How dialects extend fir, the sum, kinds of item, region kinds and a module's
dialect set are on semantics-dialects.md (ADR-2026-11-09-1543). M1 builds on
them: globals and external declarations register their kinds of item through
the hook, and a `module` item nests a symbol table with its own dialect set, so
a host module holds a device module (#211). No region kind beyond the core's
CFG region runs in M1. The round-trip and validation proofs are restated over
sums of dialects and over registered kinds of item (ADR-2026-11-09-1543).

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

This is H5 of the fir v0 decision record, and the human ruled it on 2026-11-09,
on #202. Rejected: a closed core that admits extensions only with a verified
lowering to core, as the record proposed. A quantum or photonic dialect cannot
lower to a CPU-shaped core, so it would fail G0.

## The second dialect

The second dialect in tree is shaped like a GPU kernel language
(ADR-2026-11-09-1545):

- A host module holds a nested device module whose dialect set includes the GPU
  dialect. Kernel functions live in the device module.
- It adds ops of its own, such as work-item and work-group ids and sizes, and at
  least one type or attribute of its own.
- It adds a memory in a non-default address space, such as work-group shared
  memory, with effects named by that memory.

`fir-ref` runs one work-item of a kernel, with its ids given as inputs. Ops
whose meaning needs other work-items, such as barriers, are left out or
admitted without execution rules
([fir-ref.md](fir-ref.md#an-op-without-rules)). A launch op in host code is out
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

Use-once (linear) values stay covered by the toy test of #167. Nested
modules (#211) and memory (#231) have landed.

### What holds of it today

#212 builds the dialect in four stages: its text and validation, the runs
of one work-item, work-group memory, and the generic results restated
(the stage plan on #212). All four hold:

- **Its ops.** The dialect is named `gpu`, and extends the core with no
  types of its own (`lean/Fir/Gpu/`, `crates/funk-ir/src/dialects/gpu.rs`).
  Four of its ops each ask the work-item one question in one dimension and
  give an `i32`: `gpu.work_item_id`, `gpu.work_group_id`,
  `gpu.work_group_size` and `gpu.num_work_groups`, written
  `%i: i32 = gpu.work_item_id gpu.x`. The dimension, `gpu.x`, `gpu.y` or
  `gpu.z`, is its own attribute. An op decodes from one dimension, no
  operand and one integer of any width; any other shape is a parse error,
  and validation asks for an `i32`. Their effect set is empty. A fifth,
  `gpu.work_group_alloca`, allocates in work-group memory (below). There is
  no barrier: M1 leaves out the ops that need other work-items, and an op
  without rules would break the lawful classes
  ([fir-ref.md](fir-ref.md#an-op-without-rules)).
- **Kernels.** A kernel is a function of a device module whose dialect set
  names `gpu`; `gpu` adds no rule of its own for it. The device module names
  the memories of its host's data layout (ADR-2026-11-12-1821), so its
  `alloca`, `load`, `store` and `ptradd` on `ptr(3)` validate when the host
  declares memory 3, and are rejected on both sides when it does not.
- **One work-item runs** (stage 2). The work-item is the run's input, as
  its arguments are: its id, its work-group's id, the work-group's size and
  the number of work-groups, in each dimension (`Gpu.WorkItem`). A
  question of `gpu` gives the answer, modulo 2 to the power of its width;
  it is never poison or UB and touches no memory
  (`lean/Fir/Gpu/Semantics.lean`). A kernel runs in its own table, the
  module of that table (`Module.nest`): its calls name functions of the
  device module, and its memories are its host's.
- **Its guarantees** (stages 2 to 4). The effect set of each op of `gpu`
  is proved sound at every work-item (`Gpu.lawfulDialectEffects`), and
  `gpu` is lawful with memory in its totality, monotonicity and poison
  (`lean/Fir/Gpu/WorkGroup.lean`): a question by its tie to the set monad,
  and `gpu.work_group_alloca` by its own rule, as `alloca` is. Since stage
  3, `gpu` meets no lawful class of the set monad and does not lift it, as
  the core does not: an allocation has no rule there.
  The sum `CoreGpu` keeps every guarantee of the whole core with memory
  (semantics-m1-memory.md#the-cores-guarantees), at every work-item, for
  the functions of every table of a valid module, nested at any depth: the
  four lawful classes with memory (`Gpu.coreGpu_lawfulEffects`,
  `coreGpu_lawfulTotal`, `coreGpu_lawfulMonotone`,
  `coreGpu_lawfulMemPoison`), progress and no stuck path
  (`Gpu.progress`, `Gpu.neverStuck`), refined arguments for every function
  of every module (`Gpu.args_isRefinedBy`) and congruence in the callee
  from given memories with no budget (`Gpu.replaceBody_isRefinedBy_of_from`,
  and `Gpu.caller_isRefinedBy_of_from` for the other functions), and, for a
  callee that reaches no memory, with memory (`Gpu.replaceBody_isRefinedBy`,
  `Gpu.caller_isRefinedBy`; stage 4).
  Every module of a valid module's tables is valid (`Module.Valid.nest`).
  No core statement changed. `tests/dialects/effects.cases` pins the
  effects of each op of `gpu`, on the Lean and the Rust side. Each op of
  the sum that runs by its own rule also ignores the memories where it
  declares no memory effect (`Gpu.opsIgnoreMemory`, from
  `Dialect.sum.opsIgnoreMemory` for every sum), as the congruence for a
  callee that reaches no memory asks.
- **The #231 check at run time** (stage 2, the Ordering comment on #212).
  `alloca`, `load`, `store` and `ptradd`, of integers and of pointers, run
  unchanged in a kernel on memories that its host's layout declares, other
  than memory 0, with units of 16 and 8 bits and pointers of 32 and 16 bits
  (`tests/fir/canonical/gpu-memories.fir`, `FirTest.GpuRuns`). No core op,
  theorem or `fir-ref` path needed a change: each names its memory by the
  number of its pointer type and reads its entry from the layout.
- **The tools.** `funk` reads the dialects in tree, the core and `gpu`
  (`funk_ir::dialects::in_tree`, which the corpus tests and the fuzz targets
  read too), and `fir-ref fmt`, `fir-ref validate` and `fir-ref run` read
  the sum `CoreGpu`. `fir-ref run` names a kernel as `@dev::@k` and takes
  the work-item as options (fir-ref-command-line.md#kernels-and-the-work-item);
  the corpus's interpreter-only tests give it as `work_item`
  (testing-and-harness-corpus.md). `funk build` compiles the host's functions and none of a
  device module's, as for any nested module (#211), and reports a `gpu` op
  in a top-level function as unsupported: the x86-64 backend lowers no op
  of a dialect other than the core, and `gpu` is terminal. The human ruled
  on 2026-11-16 to keep this (Q2 on #212). Rejected: reporting a module
  that holds a device module as unsupported, which changes #211's rule.
- **The G0 checks.** Generic code changed only to register it: the
  dialect's own files, `funk`'s registry and `fir-ref`'s command line name
  it. `scripts/check_g0.py` and `crates/funk-ir/tests/g0.rs` fail on a word
  of `gpu` in generic code, as on a core word (ADR-2026-11-03-0600). Its text
  is lawful and its words are its own (`Gpu.lawfulDialectText`,
  `Gpu.lawfulDialectName`), so the round trip holds for `CoreGpu` with no
  new assumption (`Gpu.printThenParse`, `Gpu.validIsWellFormed`). The
  corpus holds a host module with a device module, which both tools accept
  and print byte for byte (`tests/fir/canonical/gpu-kernel.fir`), and
  must-reject cases at both stages (`tests/fir/reject/gpu.toml`);
  `tests/dialects/gpu.cases` is read by the Lean and the Rust tests alike.

The human ruled this on 2026-11-09, on #202. Rejected: a small quantum-style
dialect, which tests neither nested modules nor several memories; it remains a
candidate for a later G0 check. Rejected too: a CPU-shaped dialect such as
checked arithmetic, which tests little of what G0 is about.

### Work-group memory

Stage 3 of #212. The human ruled on 2026-11-16, on #212 (Q1, option A):
work-group memory is an ordinary memory of the host's data layout, any
memory that it declares, with no number fixed. `gpu` owns no memory name:
its memories are the core's (`Gpu.instDialectMemOver`). It gives a declared
memory its meaning (ADR-2026-11-09-1542;
[semantics-dialects.md](semantics-dialects.md#the-sum-in-the-spec)).

- **The op.** `%p: ptr(3) = gpu.work_group_alloca i32 64 align(4)` allocates
  room for 64 `i32` in memory 3, the memory of its result, as `alloca`
  does. Its attributes are `alloca`'s after the kind: the type, the count
  when not 1 and `align(A)` when given. It writes no kind, and a kind does
  not decode. Validation has `alloca`'s rules but the kind: at least one
  value, a power-of-two alignment within the layout's limit, a valid type,
  and the data layout declares the result's memory and the memory of a
  pointer type it allocates (`Gpu.Op.Valid`, `Gpu.Op.attrTypes`). Its effect is to allocate in its result's memory,
  `allocates(N)`, as `alloca`'s is. The name and spelling are an
  implementation choice of stage 3, which the human may rule on: the name
  follows `gpu.work_group_*`, and the attributes reuse `alloca`'s reading
  (`Gpu.decodeAlloc`; `crates/funk-ir/src/dialects/core/alloc_shape.rs`).
- **Its lifetime with one work-item.** It allocates with the units and the
  alignment `alloca` would take in that memory, but with the kind `global`,
  the kind of an allocation that lives for the whole run (`Gpu.allocRule`).
  No frame records it, so no call frees it when it returns: in M1, where a
  run is the run of one work-item of a kernel, the allocation lives from
  the op until the run ends, whichever function of the device module ran
  the op. Each run of the op makes a new allocation, so an op in a loop or
  in a function called twice gives distinct blocks. The human ruled this
  on 2026-11-16 (the rulings comment on #177), to be revisited with
  several work-items (#414). Rejected: one block per op of the program, as
  a GPU's static work-group buffer is, which needs the op's identity in the
  run's state and matters only once work-items share it. A stack allocation of
  the same function is freed when its call returns. Rejected: a new kind of
  allocation, which changes the core's memory model and lets `alloca`
  decode it; and `alloca stack`, which a callee's return frees.
- **What is left for several work-items.** All the work-items of one
  work-group share one work-group allocation, and work-groups do not share
  theirs. M1 runs one work-item, so no rule says how two work-items' runs of
  the op name the same block, which work-group's block a work-item sees,
  when the block's units become poison again between work-groups, or how
  a store by one work-item is seen by a load of another; that waits for a
  concurrency model (S6) and barriers.
- **The #231 ops on it.** `ptr(N)`, `ptradd`, `load` and `store`, of
  integers and of pointers, work on work-group memory unchanged, on
  memories with units of 16 and 8 bits and pointers of 32 and 16 bits
  (`tests/fir/canonical/gpu-work-group.fir`, `FirTest.GpuRuns`,
  `tests/dialects/gpu.cases`); no core op, theorem or `fir-ref` path
  changed.
- **Floats in work-group memory.** The human ruled on 2026-11-18 (#432,
  option b) that `gpu.work_group_alloca` allocates floats, as `alloca`
  does since #264: a valid float type is an element, which takes the units
  of the integer of its `1 + e + m` bits at the natural alignment of its
  size, and the float loads and stores work on it unchanged
  (`tests/fir/canonical/gpu-work-group-floats.fir`). `Gpu.Op.Valid` drops
  `Ty.IsElem`, so its rule for an allocation is `alloca`'s but the kind.
  Rejected: integer and pointer elements only (option a), which would keep
  a kernel's f32 tile out of work-group memory though a float is stored as
  its bits in any memory.
- **Changed statements.** `Gpu.lawful` (the dialect lawful in the set
  monad) and `Gpu.instLiftsSetM` are removed, and the set-monad lemmas of
  the ops, `denote_eq`, `results_noPoison`, `results_refl`, `propagates`
  and `Op.monotone`, now speak of the questions alone
  (`Gpu.query_denote_eq` and its siblings). Every guarantee with memory of
  `gpu` and of the sum `CoreGpu` holds as before, and now covers the
  allocation too.

### The generic results restated

Stage 4 of #212. G0's generic results, which `FirTest.G0`,
`FirTest.G0Effects` and `lean/FirTest/G0/` state for every dialect, are
restated for the sum `CoreGpu`, and for the core as a base with `gpu`'s
extension, in tests of the dialect's own: `FirTest.GpuG0` (the round trip,
validation and region kinds), `FirTest.GpuG0Effects` (effects, totality
and summaries) and `FirTest.GpuG0Runs` (runs, refinement with memory,
congruence in the callee and the lawful classes of sums). Each applies the
generic theorem itself, so it builds only while that theorem stays generic
and the sum meets its hypotheses with no assumption of its own; the
`fir-spec` hook builds them, and `#check_axioms` checks them. A result
about the functions of a module holds for those of each symbol table of a
valid module, nested at any depth, run in the module of that table, so a
device module's kernels are covered, at every work-item and wherever a run
names the sum's memories. `scripts/check_g0.py` keeps `CoreGpu` out of the
generic tests (stage 1), which is why the restatements live beside them.

Every generic theorem of those files is restated but these, and the toy
behaviour models' own lemmas (`Dist.*`, `WeightedTree.*`):

- Those whose hypothesis is a dialect lawful in the set monad
  (`LawfulDialectPoison`) or one that lifts it (`LiftsSetM`). The core
  meets neither, since `alloca` has no rule in the set monad, and the sum
  fails for the same reason through `gpu.work_group_alloca`. Each has a
  statement with memory that is restated: `memProgress` for `progress`;
  `Gpu.inModuleAt_of_valid`, which `memProgress` and `memNeverStuck` use,
  for `inModuleAt`; `neverUB` and `makesNoPoison` for `neverUB_setM` and
  `makesNoPoison_setM`; the lawful classes with memory of sums for
  `lawfulTotal_ofLawful`, `lawfulMonotone_ofLawful`,
  `lawfulMemPoison_ofLawful` and `propagates`.
- `memRuns_eq` and `lawfulPoison_iff_mem`, which say that the runs with
  memory and the set monad agree. They have no counterpart: for a function
  that allocates, the set monad gives no outcome where the run with memory
  gives one, for the core alone too.
- `weightedRun`, which needs a semantics in the toy behaviour models of
  `FirTest.G0`. No dialect has one, the core included; it shows the seam,
  not a guarantee of a dialect.

The runs in the set monad that need no lawful class, `fuelMonotone` and
`neverStuck`, are restated. No proven statement was removed or narrowed.
