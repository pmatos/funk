# An op's memory effects are proved over its semantics with memory, wherever a run names the memories

Status: accepted
Tier: direction; area: semantics

## Context

ADR-2026-11-09-1541 says each op declares its effects on named memories,
and the spec proves the declaration sound: an op that does not declare a
write to *m* leaves *m* unchanged, and so on for each effect. Until now the
memory-named effects had no obligation, since no run had memory. Since
ADR-2026-11-10-2350, a run carries its memories in the state layer. Stage
2b of [#231](https://github.com/pmatos/funk/issues/231) gives these effects
their obligations. A dialect does not know how a run names its memories:
in a sum, an op of the base sees its memories under the sum's names.

## Decision

- **A semantics with memory, at every naming.** `DialectMemDenote`
  ([`MemoryObligations.lean`](../../lean/Fir/Execution/MemoryObligations.lean))
  gives each op a semantics in the state layer over the set monad, for
  every type `N` of a run's memory names, every unit width, and every map
  `ρ` from the dialect's memory names to `N`.
- **Three obligations.** `LawfulDialectEffects` gains them, for each valid
  op that runs by its own rule, at every naming `ρ` and every memory `x` of
  the run that the op's declaration, renamed by `ρ`, leaves out. A
  declaration of every memory covers every memory of the run.
  - No write (`WritesNot`): every allocation of `x` that was there before
    holds the units it held. New allocations may follow.
  - No allocation (`AllocatesNot`): `x` keeps the kind, size and liveness
    of each allocation, and the frames keep the stack allocations of `x`
    that they list. This covers freeing.
  - No read (`ReadsNot`): replace `x` by any memory with the same
    allocations. Each way the op ends from the first memories has a match
    from the second: UB for the same reason, or the same results with
    memories that agree off `x`. Each unit of `x` is then the same in both
    runs, or is in each the unit it was before. A store to `x` does not read
    `x`, although whether it faults depends on the allocations of `x`.
- **Paths that end.** UB shows no memory, so the obligations speak of the
  paths that end in results.
- **Memory-free dialects.** `DialectMemDenote.ofSetM` lifts a semantics in
  the set monad. Such a dialect meets the obligations whatever it declares.
  The core, toy, bit and probe dialects use it.
- **Sums and lifts.** A sum or a lift meets the obligations when its sides
  do. Each runs a side's op at the naming composed with its memory map
  (ADR-2026-11-11-0452).

This refines ADR-2026-11-09-1541.

## Alternatives

- **State the obligations at the dialect's own names only.** A base op in a
  sum runs at the sum's names. Nothing would then tie the base's proof to
  what the op does in the sum.
- **No write as "x unchanged".** A stack allocation would then have to
  declare a write. ADR-2026-11-09-1541 classes it as allocating only.
- **No read as "same outcomes on states that agree off x".** That allows an
  op that copies units within `x`. Dead-store elimination across such an
  op would be wrong.

## Consequences

- An op that touches memory needs a `DialectMemDenote` that runs its rule
  through the memory effect, and one proof per memory effect it leaves out.
- `observable` still has no obligation. It comes with the trace
  (ADR-2026-11-09-1540).
- Stage 2c of #231 restates progress, fuel monotonicity and refinement over
  this semantics, and ties the interpreter's runs with memory to it.
