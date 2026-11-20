# Current decisions: semantics, function summaries

This page continues semantics-effects.md with how a call carries the effects
of the function it calls. It is the record: when this page and an ADR
disagree, the page wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610).
How Rust computes the summaries is on semantics-effects.md#in-rust.

## Function summaries

A call carries its callee's effects through a summary (ADR-2026-11-09-1541):

- Each function of a symbol table has a summary: the join of what a caller
  sees of each op of each function that it reaches through calls, itself
  included (`SymbolTable.summary`, in `lean/Fir/Execution/Summary.lean`). The
  join keeps every effect of either side, and a memory-named effect touches
  the memories of both.
- A caller sees every effect of an op but control. A terminator of the callee
  ends a block of the callee, so a call is not a terminator for its caller.
  Rejected: a call carries control. Every function returns through a
  terminator, so every call would claim to be one, and the summary would say
  nothing.
- The effects of an op in place are those of its own rule and, for a call,
  its callee's summary (`SymbolTable.opEffects`).
- A call of a symbol that names no function of its table has every effect but
  control, as nothing narrower is known of it. Validation rejects such a call.
  Rejected: an unknown callee is pure, which would be unsound for a pass that
  runs before validation.
- A call resolves in the table that holds its function, so each nested
  module's functions have summaries of their own (ADR-2026-11-10-1510).
  Rejected: one table for the whole module, since a call into or out of a
  nested module is not a call that the module can make.
- The summary is the least fixpoint of the calls, recursion included
  (`SymbolTable.summary_closed`, `SymbolTable.summary_le`). In a dialect
  lawful in its effects and a module of valid functions, a function whose
  summary leaves out may-UB never ends in UB in its runs with memory, and one
  whose summary leaves out may produce poison returns no poison on arguments
  with none, at every layout and naming (`Module.summary_neverUB`,
  `Module.summary_noPoison`). They ask for no semantics in the set monad and
  no tie, so they hold for the core dialect with its memory ops (stage 4b-3b
  of #231). The proofs follow a run with memory from any memories
  (`Module.memOps_notUB`, `Module.memOps_clean`). `lean/FirTest/G0Effects.lean`
  restates them for every dialect. Rejected: keeping them over runs in the set
  monad under the tie, which no dialect with a memory op meets.
- The spec's walk and Rust's pass keep their work on the heap, so a long
  chain of calls takes no stack per call. The spec finds the functions a call
  reaches by a walk that keeps its work in lists, and Rust takes one pass over
  the call graph's strongly connected components.

Memory and observable effects join through calls like the others.
