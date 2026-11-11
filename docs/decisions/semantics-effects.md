# Current decisions: semantics, effects

This page continues semantics.md. It says what holds today about the effects
of ops. It summarizes the ADRs it cites and does not replace them. When this
page and an ADR disagree, the page is wrong (ADR-2026-11-09-1610).

## Effect sets

Each op declares a set of effects, drawn from this list
(ADR-2026-11-09-1541):

- reads memory `m`, writes memory `m`, and allocates or frees in memory `m`;
- may-UB;
- may produce poison;
- observable: it adds an event to the trace;
- control: it is a terminator.

The empty set is pure. The memory-named effects name the dialect's memories,
or every memory, as an external call needs. No op uses them yet: the core
dialect has no memory, so its memories have no names (ADR-2026-11-09-1541,
ADR-2026-11-09-1542).

An op may produce poison when, on some operands with no poison, a result may
be poison. That is not the poison class, which says how an op treats poison
operands. `select` is a poison exception and makes no poison from defined
operands, and `add` propagates poison and makes some only with a flag
(ADR-2026-11-09-2249).

The Lean class `DialectEffects`, in `lean/Fir/Execution/OpEffects.lean`, gives
each op its poison class and its effect set. `DialectPoison` folded into it
(ADR-2026-11-09-1541, ADR-2026-11-09-2249). An op's set holds the effects of
its own rule. An op with a callee also has its callee's, since its meaning is
the callee's run (ADR-2026-11-02-1514); the next section but one says how.

## The core ops' sets

`Core.Op.effects`, in `lean/Fir/Core/OpEffects.lean`, lists each core op by
its constructor, with no case for the rest. `scripts/check_g0.py` checks that,
as it checks `Core.Op.poisonClass` (ADR-2026-11-03-0600). The sets
(ADR-2026-11-09-1541, ADR-2026-11-09-2249):

- Pure: `const`, `and`, `or`, `xor`, `icmp`, `select`, the width changes,
  `freeze`, and `add`, `sub` and `mul` without flags. `call`'s own set is
  empty.
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

The memory-named effects have obligations over the op's semantics with
memory (ADR-2026-11-11-0451, in `lean/Fir/Execution/MemoryObligations.lean`):

- A dialect gives its ops a semantics in the state layer over the set monad
  wherever a run names its memories (`DialectMemDenote`): for any memory names
  of a run, any unit widths, and any map `ρ` of the dialect's memory names to
  the run's.
- For each memory `x` of the run that the op's declaration, renamed by `ρ`,
  leaves out: without a write, every allocation of `x` keeps its units
  (`WritesNot`); without allocation, `x` keeps the kind, size and liveness of
  each allocation, and the frames keep its stack allocations
  (`AllocatesNot`); without a read, the op does not depend on the units of
  `x` (`ReadsNot`). A declaration of every memory covers every memory of the
  run.
- They speak of the paths that end. A store does not read its memory: it
  writes the same units whatever was there.

All but the last obligation cover valid op instances that are terminators
or have no callee, as the poison obligations do (ADR-2026-11-02-1514).
Observable has no obligation yet: M0's runs have no trace. The core dialect
is lawful in its effects (`Core.lawfulDialectEffects`). Its ops touch no
memory, so `DialectMemDenote.ofSetM` gives its semantics with memory and
meets every memory obligation. `lean/FirTest/G0Effects.lean` restates the
class and its obligations for every dialect. The obligations reject a wrong
declaration: with `sdiv` declared without may-UB, the core dialect is not
lawful in its effects (`Core.Unlawful.sdivNoUB_unlawful`). And
`lean/FirTest/MemoryObligations.lean` shows that an allocation allocates, a
store writes and a load reads.

A sum of dialects gives each op its own side's effects, on the sum's
memories, where a memory has one name (ADR-2026-11-11-0452). A lift gives
each op of the extension its effects in the extension, renamed by its memory
map. The sum of dialects lawful in their effects is lawful in its effects,
and so is a lift, under the conditions that make them lawful for poison
(`Dialect.sum.lawfulEffects`, `Dialect.lift.lawfulEffects`;
ADR-2026-11-09-2306, ADR-2026-11-10-1310). A side's op meets the memory
obligations in the sum at the run's naming composed with the side's memory
map. The toy and bit test dialects declare pure ops and are lawful in their
effects, and so are their sums with the core. The probe test dialect
declares every effect and is lawful in its effects, and so is its sum with
the core.

## Function summaries

A call carries its callee's effects through a summary (ADR-2026-11-10-2108,
refining ADR-2026-11-09-1541):

- Each function of a symbol table has a summary: the join of what a caller
  sees of each op of each function that it reaches through calls, itself
  included (`SymbolTable.summary`, in `lean/Fir/Execution/Summary.lean`). A
  caller sees every effect of an op but control.
- The effects of an op in place are those of its own rule and, for a call,
  its callee's summary (`SymbolTable.opEffects`). A call of a symbol that
  names no function of its table has every effect but control.
- A call resolves in the table that holds its function, so each nested
  module's functions have summaries of their own (ADR-2026-11-10-1510).
- The summary is the least fixpoint of the calls, recursion included
  (`SymbolTable.summary_closed`, `SymbolTable.summary_le`). In a dialect
  lawful in its effects and a module of valid functions, a function whose
  summary leaves out may-UB never ends in UB, and one whose summary leaves
  out may produce poison returns no poison on arguments with none
  (`Module.summary_neverUB`, `Module.summary_noPoison`).
  `lean/FirTest/G0Effects.lean` restates them for every dialect.
- The spec's walk and Rust's pass keep their work on the heap, so a long
  chain of calls takes no stack per call.

## In Rust

`funk-ir` mirrors the class (ADR-2026-11-09-1541). `Effects`, in
`crates/funk-ir/src/effects.rs`, has the fields of the Lean `Effects`, with
memories named by strings. `OpSpec::effects` is required, so every op of
every Rust dialect declares its set, the test dialects included.
`Registry::effects` gives an op's set through the dialect that its prefix
names, as a sum gives each op its own side's set (ADR-2026-11-10-0042). No
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
Lean. `tests/dialects/effect-summaries.cases` pins the summary of every
function of its modules, nested ones included; `lean/FirTest/SummaryCases.lean`
and `crates/funk-ir/tests/summaries.rs` read it, so Rust's summaries equal
`SymbolTable.summary` (ADR-2026-11-10-2108).
