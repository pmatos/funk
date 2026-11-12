# A call carries its callee's summary: the effects of every op that it may reach, but control

Status: accepted
Tier: direction; area: semantics

## Context

ADR-2026-11-09-1541 gives each op a set of effects and says that `call`
carries its callee's effects. ADR-2026-11-02-1514 gives a call no rule of
its own: its meaning is its callee's run. So an op's declared set holds
only its own rule's effects, and `call`'s is empty (`Core.Op.effects`).
A pass that reads a call's effects needs the callee's too, and the
callee's callees', through recursion. Modules nest, and each module holds a
symbol table of its own (ADR-2026-11-10-1510).

## Decision

- **The summary.** Each function of a symbol table has a summary: the join
  of what a caller sees of each op of each function that it reaches through
  calls, itself included (`SymbolTable.summary` in
  [`Summary.lean`](../../lean/Fir/Execution/Summary.lean)). The join keeps
  every effect of either side, and a memory-named effect touches the
  memories of both.
- **What a caller sees.** Every effect of an op but control. A terminator
  of the callee ends a block of the callee, so a call is not a terminator
  for its caller.
- **A call in place.** The effects of an op in place are those of its own
  rule and, when it calls a function, its callee's summary
  (`SymbolTable.opEffects`).
- **An unknown callee.** A call of a symbol that names no function of its
  table has every effect but control, as nothing narrower is known of it.
  Validation rejects such a call.
- **Per table.** A call resolves in the symbol table that holds its
  function, so each table's functions have their own summaries.
- **Proved.** The summary is the least fixpoint of the calls
  (`SymbolTable.summary_closed`, `SymbolTable.summary_le`). It is sound for
  every dialect lawful in its effects, in a module of valid functions: a
  function whose summary leaves out may-UB never ends in UB
  (`Module.summary_neverUB`), and one whose summary leaves out may produce
  poison returns no poison on arguments with none
  (`Module.summary_noPoison`, ADR-2026-11-09-2249).
- **No stack per call.** The spec finds the functions a call reaches by a
  walk that keeps its work in lists. Rust's `Summaries` takes one pass over
  the call graph's strongly connected components, with its path on the heap
  ([rust-ir-and-tools.md](../decisions/rust-ir-and-tools.md#nesting)). A summary is a set, so Rust keeps its memories
  sorted. `tests/dialects/effect-summaries.cases` checks that Rust's
  summaries equal Lean's.

## Alternatives

- **A call carries control.** Every function returns through a terminator,
  so every call would claim to be one, and the summary would say nothing.
- **An unknown callee is pure.** Validation rules it out, but a pass may run
  on a module before validation, and pure would be unsound for it.
- **One table for the whole module.** A call into or out of a nested module
  is not a call that the module can make (ADR-2026-11-10-1510).

## Consequences

- A pass reads a call's effects from one place, and the reading is proved.
- Memory and observable effects join through calls like the others. Their
  soundness obligations come with the memory model and the trace, as they
  do for single ops.
