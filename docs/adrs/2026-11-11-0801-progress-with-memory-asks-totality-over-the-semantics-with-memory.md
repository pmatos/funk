# Progress with memory asks each op to be total over the semantics with memory, and is proved beside progress in the set monad

Status: accepted; refined by ADR-2026-11-11-1002
Tier: direction; area: semantics

## Context

Progress in the set monad asks each op that runs by its own rule to be
total there (`OpTotal`, in `LawfulDialectPoison`). An op that touches
memory has no semantics in the set monad (ADR-2026-11-11-0623), so that
obligation says nothing of a load or a store, and progress said nothing of
runs with memory beyond the dialects that lift the set monad. `Func.InModule`
has the same gap: its rules for terminators speak of their exits in the set
monad. Stage 2c-2 of [#231](https://github.com/pmatos/funk/issues/231)
gives runs with memory their progress before the first memory op lands
(stage 4).

The 2c-1 review left a choice to 2c-2 and 2c-3: derive the set-monad
theorems from the state-layer ones, or prove the state-layer ones beside
them. `Calls.lean` and `Monotone.lean` sit below `Lawful.lean` and
`MemoryRuns.lean`, which the state-layer proofs import, and their lemmas
feed `RunPaths`, `BlackBox`, the core's corollaries and their readable
pages.

## Decision

- **Totality is stated over the semantics with memory.** `MemTotal op`
  ([`MemoryTotal.lean`](../../lean/Fir/Execution/MemoryTotal.lean)) holds
  when, at every naming of the dialect's memories and from any memories,
  what the op runs by its own rule has an outcome (`HasOutcome`): a result
  with the memories after it, or UB.
- **The obligation is a class of its own.** `LawfulDialectTotal d` asks
  `MemTotal` of every valid op instance that is a terminator or has no
  callee. It asks for no semantics in the set monad. It is not a field of
  `LawfulDialectEffects` (totality is not an effect) nor of
  `LawfulDialectPoison` (which asks for a semantics in the set monad).
  `OpTotal` and `LawfulDialectPoison.total` stay for runs in the set monad.
- **The tie gives it.** Under `LiftsSetM`, `MemTotal` and `OpTotal` agree
  (`MemTotal.ofLifts`, `MemTotal.setM`), and a lawful dialect is lawful in
  its totality (`LawfulDialectTotal.ofLawful`). The core, toy, bit and probe
  dialects meet it so. Sums and lifts are lawful in their totality when
  their sides are (`Dialect.sum.lawfulTotal`, `Dialect.lift.lawfulTotal`),
  with no tie, so a side whose ops touch memory may take part.
- **Running within a module has a memory form.** `Func.MemInModule` states
  the rules for terminators over their exits in the state layer, from any
  memories; `Func.InModuleAt unit ρ M f` is it at a naming. Under
  `LiftsSetM`, `Func.InModule` gives it (`Func.InModule.inModuleAt`).
- **Progress with memory is proved beside progress in the set monad, not
  derived from it or into it.** `Func.memNeverStuck` and `Func.memProgress`
  ([`MemoryProgress.lean`](../../lean/Fir/Execution/MemoryProgress.lean))
  follow the proofs of `Calls.lean` step by step through the path calculus
  of `StatePaths.lean`, as `MemoryMonotone.lean` does for fuel
  monotonicity. They replace `Func.memProgress_of_lawful`, which needed the
  tie.

This refines ADR-2026-11-11-0623.

## Alternatives

- **Derive the set-monad theorems from the state-layer ones.** One proof
  instead of two, but it moves `Ahead`, `LeavesAtMost`, the path calculus
  and the state-layer proofs below `Calls.lean` and `Monotone.lean`, and
  rewrites their clients and readable pages. Done for progress alone, the
  three theorems would follow two patterns. It is one refactor over fuel
  monotonicity, progress and refinement, once stage 2c-3 lands, and needs
  its own ticket.
- **Move `total` from `LawfulDialectPoison` to the semantics with memory.**
  The set-monad theorems would then need the tie to use it, and
  `LawfulDialectPoison` still asks for a semantics in the set monad that a
  memory dialect cannot give.

## Consequences

- Every dialect's runs with memory have no stuck path when its module's
  functions are valid and run within the module with memory, and have
  progress when it is lawful in its totality, whatever its ops do to the
  memories. A valid core module meets both (`Core.memNeverStuck`,
  `Core.memProgress`).
- A dialect with a memory op proves `LawfulDialectTotal` directly; the
  tests' alloc dialect does.
- Each change to `Func.runOps` must be proved in both `Calls.lean` and
  `MemoryProgress.lean`, as in both monotonicity files, until the refactor
  above.
