# Current decisions: semantics, effects

This page continues semantics.md. It says what holds today about the effects of
ops. It is the record: when this page and an ADR disagree, the page wins, and
the ADR is fixed or deleted (ADR-2026-11-09-1610). ADR-2026-11-09-1541 holds the
direction decision, and semantics-m1-design.md says how M1's ops will use it.

## Effect sets

Each op declares a set of effects, drawn from this list
(ADR-2026-11-09-1541):

- reads memory `m`, writes memory `m`, and allocates or frees in memory `m`;
- may-UB;
- may produce poison;
- observable: it adds an event to the trace;
- control: it is a terminator.

The human ruled this on 2026-11-09, on #208. Rejected: one effect class per op,
as the decision record proposed. A load reads memory, may hit UB and may produce
poison at once, so it would lose its may-UB or fall into a catch-all class.
Rejected too: effect sets that do not name a memory, since accesses to different
memories could then never be reordered.

The empty set is pure. The memory-named effects name the dialect's memories,
or every memory, as an external call needs. No op uses them yet: the core
dialect has no memory, so its memories have no names (ADR-2026-11-09-1541,
ADR-2026-11-09-1542).

An op may produce poison when, on some operands with no poison, a result may
be poison: LLVM's `canCreatePoison`. That is not the poison class, which says
how an op treats poison operands. `select` is a poison exception and makes no
poison from defined operands, and `add` propagates poison and makes some only
with a flag (ADR-2026-11-09-1541). The human approved this as option B on
2026-11-10, on #226. Rejected: the effect is the class, `propagates` meaning may
produce poison. It is sound under the obligation below, but `const`, `icmp`, the
bitwise ops, the width changes and `add` without flags would all be marked as
producing poison, so an analysis would learn nothing from them. Rejected too:
the effect means "a result may be poison", which nearly every op has.

The Lean class `DialectEffects`, in `lean/Fir/Execution/OpEffects.lean`, gives
each op its poison class and its effect set, so an op's poison behaviour is
declared in one place. `DialectPoison` folded into it, and the class keeps its
meaning and its obligations (ADR-2026-11-09-1541). An op's set holds the effects
of its own rule. An op with a callee also has its callee's, since its meaning is
the callee's run (ADR-2026-10-29-2006); the section on function summaries says
how.

## The core ops' sets

`Core.Op.effects`, in `lean/Fir/Core/OpEffects.lean`, lists each core op by
its constructor, with no case for the rest. `scripts/check_g0.py` checks that,
as it checks `Core.Op.poisonClass` (ADR-2026-11-03-0600). The sets
(ADR-2026-11-09-1541):

- Pure: `const`, a float's included, `and`, `or`, `xor`, `icmp`, `fcmp`,
  `select`, the width changes, `freeze`, `add`, `sub` and `mul` without
  flags, and the float arithmetic, whose NaN results are defined values
  (ADR-2026-11-09-1549). `call`'s own set is empty: its callee's summary
  carries its effects (ADR-2026-11-09-1541).
- May produce poison: `poison`, the shifts, `add`, `sub` and `mul` with a
  flag, and `sdiv` and `udiv` with `exact`.
- May-UB: the four divisions, `cond_br` and `unreachable`.
- Control: `br`, `cond_br`, `ret` and `unreachable`.

## Soundness

`LawfulDialectEffects`, in `lean/Fir/Execution/EffectLaws.lean`, holds the
obligations of each effect an op leaves out (ADR-2026-11-09-1541):

- Without may-UB, the op never ends in UB, and neither does a terminator's
  exit.
- Without may produce poison, the op gives no poison on operands with no
  poison.
- Without control, the op is not a terminator.

The first two are stated over the op's semantics with memory, wherever a
run names the dialect's memories and from any memories (`NeverUB`,
`MakesNoPoison`), so they hold of an op that touches memory too. The class
asks for no semantics in the set monad; the set-monad forms remain as
`NeverUBSetM` and `MakesNoPoisonSetM`. Rejected: keep these two in the set
monad beside the memory obligations, which would ask a dialect with memory ops
for a semantics in the set monad that it cannot give.

The memory-named effects have obligations over the op's semantics with
memory, in `lean/Fir/Execution/MemoryObligations.lean`:

- A dialect gives its ops a semantics in the state layer over the set monad
  wherever a run names its memories (`DialectMemDenote`): for any memory names
  of a run, any unit widths, and any map `ρ` of the dialect's memory names to
  the run's. The module's data layout, not the dialect, gives the widths
  (ADR-2026-11-10-2350).
- For each memory `x` of the run that the op's declaration, renamed by `ρ`,
  leaves out: without a write, every allocation of `x` that was there keeps
  its units, and new allocations may follow (`WritesNot`); without
  allocation, `x` keeps the kind, size and liveness of each allocation, and
  the frames keep its stack allocations, which covers freeing
  (`AllocatesNot`); without a read, the op does not depend on the units of
  `x` (`ReadsNot`). A declaration of every memory covers every memory of the
  run.
- `ReadsNot` replaces `x` by any memory with the same allocations. Each way
  the op ends from the first memories has a match from the second: UB for the
  same reason, or the same results with memories that agree off `x`, where
  each unit of `x` is the same in both or is in each the unit it was before.
- No write and no allocation speak of the paths that end in results, since UB
  shows no memory; no read matches UB with UB. A store does not read its
  memory: it writes the same units whatever was there, although whether it
  faults depends on the allocations (`lean/FirTest/MemoryStoreReads.lean`).

Rejected: the obligations at the dialect's own memory names only. A base op in
a sum runs at the sum's names, and nothing would tie the base's proof to what
the op does there. Rejected: no write as "`x` unchanged", which would make a
stack allocation declare a write. Rejected: no read as "the same outcomes on
states that agree off `x`", which allows an op that copies units within `x`, so
dead-store elimination across it would be wrong.

Every obligation but control's covers valid op instances that are
terminators or have no callee, as the poison obligations do
(ADR-2026-10-29-2006).

A dialect whose ops touch no memory ties its two semantics: `LiftsSetM`, in
`lean/Fir/Execution/MemoryRuns.lean`, says that its semantics with memory is its
semantics in the set monad, lifted, at every naming. `DialectMemDenote.ofSetM`
meets it, and so do sums and lifts whose sides do. Under the tie an op meets no
may-UB and no may produce poison in the set monad exactly when it meets them
with memory (`NeverUB.setM`, `MakesNoPoison.setM`, and `.ofSetM` back), and
theorems over runs in the set monad that use these two obligations assume the
tie. Theorems that do not use them, such as fuel monotonicity, progress and
refinement of runs in the set monad, take no tie. A dialect with a memory op has
no tie: its theorems speak of its runs with memory. Runs with memory,
`Func.memRuns unit ρ M f`, run `DialectMemDenote.denoteAt unit ρ` from the empty
memories, and under the tie they are the runs in the set monad
(`Func.memRuns_eq`). Rejected: a tie for every dialect, memory ops included. A
load has no meaning in the set monad, so the tie would make it UB or give it no
outcome there, and the runs in the set monad would mean nothing for programs
that touch memory.

Observable has no obligation yet: M0's runs have no trace. The core dialect is
lawful in its effects (`Core.lawfulDialectEffects`). Its ops touch no memory, so
`DialectMemDenote.ofSetM` gives its semantics with memory and meets every memory
obligation, whatever it declares. `lean/FirTest/G0Effects.lean` restates the
class and its obligations for every dialect. The obligations reject a wrong
declaration: with `sdiv` declared without may-UB, the core dialect is not lawful
in its effects (`Core.Unlawful.sdivNoUB_unlawful`). And
`lean/FirTest/MemoryObligations.lean` shows that an allocation allocates, a
store writes and a load reads.

A sum of dialects gives each op its own side's effects, on the sum's
memories, where a memory has one name (ADR-2026-11-09-2306). A lift gives
each op of the extension its effects in the extension, renamed by its memory
map. The sum of dialects lawful in their effects is lawful in its effects,
and so is a lift, under the conditions that make them lawful for poison
(`Dialect.sum.lawfulEffects`, `Dialect.lift.lawfulEffects`;
ADR-2026-11-09-2306). A side's op meets the memory obligations in the sum at
the run's naming composed with the side's memory map. The toy and bit test
dialects declare pure ops and are lawful in their effects, and so are their
sums with the core. The probe test dialect declares every effect and is lawful
in its effects, and so is its sum with the core.

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
  lawful in its effects that lifts the set monad, and a module of valid
  functions, a function whose summary leaves out may-UB never ends in UB, and
  one whose summary leaves out may produce poison returns no poison on
  arguments with none (`Module.summary_neverUB`, `Module.summary_noPoison`).
  `lean/FirTest/G0Effects.lean` restates them for every dialect. When the core
  dialect gains a memory op (stage 4 of #231), it no longer lifts the set
  monad, and these two theorems need statements over runs with memory first.
- The spec's walk and Rust's pass keep their work on the heap, so a long
  chain of calls takes no stack per call. The spec finds the functions a call
  reaches by a walk that keeps its work in lists, and Rust takes one pass over
  the call graph's strongly connected components.

Memory and observable effects join through calls like the others.

## In Rust

`funk-ir` mirrors the class (ADR-2026-11-09-1541). `Effects`, in
`crates/funk-ir/src/effects.rs`, has the fields of the Lean `Effects`, with
memories named by strings. `OpSpec::effects` is required, so every op of
every Rust dialect declares its set, the test dialects included.
`Registry::effects` gives an op's set through the dialect that its prefix
names, as a sum gives each op its own side's set (ADR-2026-10-30-1146). No
registered dialect has a memory yet, so how Rust keeps each dialect's
memories apart is left to the first dialect that adds one.

`tests/dialects/effects.cases` pins the set of every core op, at each
attribute that changes it. `lean/FirTest/EffectCases.lean` and
`crates/funk-ir/tests/effects.rs` read it, so the `fir-spec` and `rust-test`
hooks check that Rust's sets equal `Core.Op.effects`, as the use-once cases
check the two validators (ADR-2026-11-09-2257).

`Summaries`, in `crates/funk-ir/src/summary.rs`, gives each function of a
table its summary, and each op in place its effects with its callee's.
`OpSpec::callee` names the function that an op calls, as `callee?` does in
Lean. A summary is a set, so Rust keeps its memories sorted.
`tests/dialects/effect-summaries.cases` pins the summary of every function of
its modules, nested ones included; `lean/FirTest/SummaryCases.lean` and
`crates/funk-ir/tests/summaries.rs` read it, so Rust's summaries equal
`SymbolTable.summary` (ADR-2026-11-09-1541).
