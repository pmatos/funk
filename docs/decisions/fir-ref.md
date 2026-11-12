# Current decisions: fir-ref

This page states what holds today for `fir-ref`, the reference interpreter's
executable. It is the record: when this page and an ADR disagree, the page wins,
and the ADR is fixed or deleted (ADR-2026-11-09-1610). It continues in
[fir-ref-command-line.md](fir-ref-command-line.md) (what each command takes and
prints), [fir-ref-fast-paths.md](fir-ref-fast-paths.md) (each implementation
`fir-ref` runs in place of a spec function, and what it is for) and
[fir-ref-memory.md](fir-ref-memory.md) (runs with memory).

## What a run means

`freeze` of poison is a choice. The interpreter's monad has a `choose w`
effect, and `freeze` of poison calls it. Every use of the result sees the
same bits. In the set instance of the monad, the interpreter defines the
semantics: the set of behaviours over all choices. The human made this call on
2026-10-29 (#7), with the soundness proofs and declared results with
witnesses (ADR-2026-10-29-2017).

The same interpreter backs every mode. Exhaustive mode tries every choice
sequence within a budget and prints the set of outcomes. Scripted mode takes
one choice sequence and prints one outcome. Lean proves that exhaustive mode,
within its budget, returns exactly the semantic set. Lean also proves that
scripted mode returns a member of it. So the oracle the harness runs is the
semantics the spec defines (ADR-2026-10-29-2017).

Rejected: one fixed value for `freeze` of poison, which fails correct native
code; and any native value when `freeze` is involved, which misses `x xor x`
returning non-zero (ADR-2026-10-29-2017).

Every op takes one step of fuel, a call included. A callee runs with the
fuel its caller has left, and the caller goes on with what the callee gives
back. A callee that runs out of fuel ends the run that way. Its UB and stuck
paths are its caller's (ADR-2026-11-02-0836).

A call has no op-level rule. Its meaning is its callee's run. The interpreter
runs the callee of every op that has one before it looks at `denote`.
`Core.Op.denote?` gives `none` for `call`, but `call` does not count as an op
without rules (ADR-2026-11-02-1514).

### The tree of choices

The spec's meaning of a run is `Func.run` in the set monad `SetM`. A program
cannot list a predicate's members, so the spec also has `ChoiceTree`, a monad
whose computations are trees (`lean/Fir/Execution/ChoiceTree.lean`). A leaf
ends a path with a result, with UB, or with no outcome for a reason.
A node `choose w k` has a subtree for each `w` bits. The core dialect's rules
are written once for any monad, and run in `ChoiceTree Core.Op`, where an op
without rules ends its path with no outcome and names itself.

`ChoiceTree.toSet` maps a tree to the set of ways its paths end. It is a
monad morphism, and a path with no outcome adds nothing. `Func.run_map`
proves that such a morphism carries a run in one monad to the run in the
other. `Core.mapsDenote` proves that the core rules in the tree map to those
in `SetM`. `ChoiceTree.explore` and `ChoiceTree.script` are the two walks,
proved sound once for any tree (`explore_toSet`, `script_toSet`), and lifted
to a run of any dialect by `Func.explore_outcomes` and `Func.script_outcomes`.
`Core.exhaustive_outcomes` and `Core.scripted_outcomes` state the results for
the core dialect, about the functions `fir-ref` calls, `Core.exhaustive` and
`Core.scripted`. A node holds a function of the bits, so exhaustive mode runs
the rest of the function once for each value it tries.

A new op family adds its rule to `Core.Op.denote?` or `Core.Op.exit?`, and
`Core.mapsDenote` covers it, usually by `rfl`. A new effect needs its node in
the tree, its image in the set monad, and its case in the morphism's proofs.
Calls need none of these, since the interpreter's call path uses only `pure`,
`bind` and `liftExcept` (ADR-2026-11-02-0836). A change to the interpreter
that uses another monad operation extends `Func.runOps_map`'s proof.

Rejected: a list monad that carries every path. Scripted mode would need a
second monad and a second proof; one tree gives both walks from one run. Also
rejected: defining the semantics through the tree, since the spec's
`DialectDenote CoreDialect SetM` is the contract.

### An op without rules

`Core.Op.denote?` and `Core.Op.exit?` give each core op its family's rule, or
`none` while its family has not landed (`lean/Fir/Core/Semantics.lean`). `call`
gives `none` too, but its meaning is its callee's run (ADR-2026-11-02-1514). In
`DialectDenote CoreDialect SetM`, an op without rules has no outcome: the empty
set on every operand vector. A run that reaches it has no way to end on that
path. `fir-ref run` reports it as an error, never as stuck or UB
([the command line](fir-ref-command-line.md#exit-status-and-errors)), and the
harness sees a tool error, never a wrong result.

Only totality, `ReturnsOnDefined`, progress and the lawful class reject a
missing rule, so `LawfulDialectPoison CoreDialect` cannot be proved while an
op lacks its rules. `PropagatesPoison`, `OpMonotone`, `NeverStuck` and
`FuelMonotone` hold trivially there, since the empty set meets every bound. So
none of them is stated of such an op, or of a function that reaches one.

Rejected: every outcome, which looks lawful for `br`, `select`, `freeze` and
`call`, and which `fir-ref` cannot print; always UB, which is wrong for every
such op and makes the harness call the test invalid; and stuck, which means
invalid, while these modules are valid.

## What the harness takes from a run

The harness judges a native result by refinement against the set of outcomes
that `fir-ref` gives: a poison outcome matches any native value, and seeded
checks only sample, so they can miss a rare outcome (ADR-2026-10-29-2017). The
rules, declared results and witnesses included, are on
[testing-and-harness.md](testing-and-harness.md#how-a-test-is-judged)
(ADR-2026-10-30-2135).

### Poison arguments

The human ruled on 2026-11-03 that `fir-ref run` takes `poison` as an argument,
as in `fir-ref run f.fir @g 3 poison`, and that the harness uses it in
differential tests too (#123). How the harness runs native code on stand-ins
in its place, and why that is sound, is on
[testing-and-harness.md](testing-and-harness.md#poison-arguments).

## How fir-ref stays equal to the spec

fir has no nesting limit. So `fir-ref` must give a verdict on a text nested
to any depth, without a stack overflow (ADR-2026-10-30-1549). The spec's
functions stay readable recursive definitions in `lean/Fir/`, and the proofs
about them hold for what `fir-ref` runs (ADR-2026-10-30-1450).

A spec function on `fir-ref`'s path that takes stack per level of nesting, per
list element, per step or per call gets an implementation proved equal to it. The
implementation is a loop whose recursive calls are all tail calls. It keeps
what is left to do on an explicit stack of frames. It writes its output into
one accumulator. It is defined by well-founded recursion on a measure of its
frames, so it is total and has no fuel (ADR-2026-10-30-1450).

Each implementation is registered with `@[csimp] theorem : @specFn =
@fastFn`. The proofs use no `sorry`, `partial`, `unsafe`, `implemented_by` or
`native_decide`. They use only `propext`, `Classical.choice` and
`Quot.sound`, which the Lean build checks. The implementations live in
`lean/FirRef/`, which the document does not render. `lean/Fir/` does not
change for them (ADR-2026-10-30-1450).

Rejected: `implemented_by`, which proves nothing; and rewriting the spec's
functions as loops, which would lose the readable definitions the proofs are
about (ADR-2026-10-30-1450).

`@[csimp]` acts only on code compiled after the theorem is in scope. So
compile order is part of the rule (ADR-2026-10-30-1450):

- `FirRef.Fast` imports every module that registers such a theorem, and
  `FirRef.Utf8` imports `FirRef.Fast`.
- `FirRef.Main` and `FirTest` import `FirRef.Utf8`.
- A module of `FirRef` that calls the spec's parser or printer must import
  `FirRef.Fast`, directly or through `FirRef.Utf8`.
- A theorem reaches an implementation only if the implementation's own module
  imports it. A spec function compiled before a theorem keeps the slow code,
  so a caller that matters is replaced whole, as `FirRef.parse` replaces
  `Fir.parse`.

The run modes are an exception to the `FirRef.Fast` rule. Their theorems
name the core dialect, and in `lean/FirRef/` only `fir-ref`'s command line
may (ADR-2026-11-03-0600). So they sit in `FirRef.Run`, which `FirRef.Fast`
does not import ([Running](fir-ref-fast-paths.md#running)).

A change to a spec function breaks its theorem's proof, and so the build,
until the implementation follows. The `#guard` checks and `#eval`s of
`FirTest` run the implementations. The checks inside `lean/Fir/` run the
spec's definitions. The evidence that `fir-ref` runs an implementation is in
the C that Lean emits under `lean/.lake/build/ir/FirRef/`
(ADR-2026-10-30-1450).

### When a new fast path is allowed

A new fast path needs the depth rule above, or a case that is clearly too slow.
More than linear time is not enough on its own. "Clearly too slow" means what
the human's speed ruling of 2026-11-05 means by it: Lean-side speed is not a
concern, about 10x of the Rust side on the same job is a rough guide, not a
gate, and hours on a simple example is not fine
([#5](https://github.com/pmatos/funk/issues/5#issuecomment-6506908304)). Such a
case is raised to the human, and starting a fast path for speed is a new
performance ticket, which needs the human first (ADR-2026-11-06-0744). The
speed ruling does not cover memory, and no new fast path is admitted for memory
alone (ADR-2026-10-30-1450).

The existing speed-only fast paths stay. The human ruled on 2026-11-09 (#169)
that `lean/FirRef` stays as it is: each fast path is proved equal to the spec,
so keeping one costs no trust, and none can go without making `fir-ref` far
slower. The same day the human ruled that the bindings map stays.
[fir-ref-fast-paths.md](fir-ref-fast-paths.md#what-each-fast-path-is-for)
lists each fast path with its class.

Rejected: keeping "more than linear time" as the trigger, which asks for speed
work that the speed ruling says is not needed (ADR-2026-10-30-1450).
