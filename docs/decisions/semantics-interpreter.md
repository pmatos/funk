# Current decisions: semantics, the interpreter

This page continues semantics.md. It says what holds today about the Lean
interpreter that defines fir's meaning: its calculus, calls and fuel, and the
proofs that no run gets stuck. It is the record: when this page and an ADR
disagree, the page wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610).
ADR-2026-10-29-2009 and ADR-2026-11-02-2248 hold the direction decisions.

## A monadic interpreter with fuel

fir's semantics is a monadic definitional interpreter, written in Lean. It is
not built on interaction trees. Fuel bounds every run, so the interpreter always
terminates. A run that uses all its fuel ends with fuel exhausted. Fuel
exhaustion is an outcome of its own, beside a value, poison and UB. It stands
for non-termination (ADR-2026-10-29-2009). This is S7. Rejected: interaction
trees, as in Vellvm, since a fuelled interpreter is a total function that Lean
runs directly and that proofs unfold case by case.

It is the only interpreter: a test oracle for development and CI, run as
`fir-ref`. It never ships inside a compiler. Lean holds the semantics, the
interpreter and its own `.fir` parser and printer. Rust holds the whole
toolchain: the IR library, verifier, passes, backends and driver. There is no
Rust interpreter in M0. One may come later only as a copy tested against Lean,
never as the definition (ADR-2026-10-29-2009). Hand-written Rust, such as the
backend, is checked against this interpreter, so its speed bounds how much the
harness can test.

## Its own calculus

fir's Lean semantics is its own calculus. It takes no dependency on LeanMLIR,
and keeps LeanMLIR's shape wherever that is cheap (ADR-2026-10-29-2009):

- A dialect is a structure with `Op` and `Ty`.
- `TyDenote` gives each type its meaning.
- `DialectSignature` gives each op its operand and result types.
- Each op's semantics has the shape of LeanMLIR's `DialectDenote.denote`.
- Values of `iN` are `PoisonOr (BitVec N)`, fir's own type.
- Refinement is written through a heterogeneous class shaped like LeanMLIR's
  `HRefinement`. That fixes only the notation.

It differs from LeanMLIR on purpose in four places (ADR-2026-10-29-2009):

- Terms are extrinsically typed. Values have names, every op has a location,
  and a function is a CFG of blocks with arguments and successors. Typing is a
  separate validation judgement.
- Terminators are ops that `DialectSignature.isTerminator` marks. Their
  semantics is `DialectDenote.exit`, which returns an `Exit`: a successor
  index, or return.
- A dialect does not fix one monad. Its semantics states the effects it needs
  as class constraints on the monad, such as `choose w` and immediate UB.
- The parser and printer are fir's own, over the extrinsic syntax.

Operands travel in an `HVector`, so per-op semantics port between the two
mechanically. A port adjusts for what LeanMLIR does otherwise: its `denote`
also takes the op's regions and runs pure ops outside the dialect monad, it
has no successors, so a terminator becomes an op that returns a control value,
and fir's `PoisonOr` is its own type, with `poison` and `value` named as in
LeanMLIR, so a port converts values. The encoding admits sum dialects, as
LeanMLIR's `Scf` functor does (ADR-2026-11-09-2306).

The human chose this on 2026-10-29, in PR #27, after the spike of #24, whose
report is `docs/spikes/leanmlir.md`. Rejected: depending on LeanMLIR, which has
no CFG, no op locations and no value names, and is frozen on a Lean nightly;
forking it, which means porting it and Mathlib to each Lean release ourselves;
and building on VeIR, whose coinductive choice trees conflict with S7, and
which stubs out locations and has no value names. VeIR comes back only if S7 is
reopened.

The term carries op regions from M0 on, empty for core ops. Kinds and rules
of regions: ADR-2026-11-10-1941. The CFG is the core dialect's region kind.
Extensions compose as ADR-2026-11-09-1543 and ADR-2026-11-09-1544 say. Verified
rewrites (M2) mean fir's own refinement-based rewrite framework, or VeIR if S7
is reopened. We give up LeanMLIR's rewriter, DCE, CSE and tactics; `bv_decide`
is part of Lean and stays available (ADR-2026-10-29-2009).

## Memory and progress with memory

Memory is an effect of a run. The state layer `StateT` over the way of
computing carries the memories of a run, and the interpreter runs every
function in a frame, which frees the function's stack allocations when it
returns. In a monad with no memory, such as the set monad or the tree of
choices, a frame changes nothing, so M0's runs are unchanged
(ADR-2026-11-10-2350). A function's runs with memory run its dialect's
semantics with memory at a naming of the memories, from the empty
memories. They are fuel-monotone for every dialect, and for a dialect that
lifts the set monad they are its runs (semantics-effects.md).

Runs with memory have progress for every dialect, whatever its ops do to the
memories. No path is stuck when every function of the module is valid and
runs within it with memory, at the run's naming (`Func.InModuleAt`, which
states the rules for terminators over their exits from any memories; under
`LiftsSetM`, `Func.InModule` gives it). Each
run has an outcome at every budget when the dialect is also lawful in its
totality (`LawfulDialectTotal`, in `lean/Fir/Execution/MemoryTotal.lean`):
each valid op that is a terminator or has no callee has an outcome from any
memories, at every naming (`MemTotal`). That class asks for no semantics in the
set monad, and is not a field of `LawfulDialectEffects`, since totality is not
an effect. `OpTotal` stays for runs in the set monad. A dialect that lifts the
set monad and is lawful meets it, and so do sums and lifts whose sides do,
with no tie, so a side whose ops touch memory may take part. A dialect with a
memory op proves it directly. A valid core module meets both
(`Core.memNeverStuck`, `Core.memProgress`). Rejected: moving `total` out of
`LawfulDialectPoison` to the semantics with memory, since the set-monad
theorems would then need the tie to use it.

These proofs, in `lean/Fir/Execution/MemoryProgress.lean`, stand beside those
for runs in the set monad, step by step, through the path calculus of
`StatePaths.lean`. So each change to `Func.runOps` is proved in both
`Calls.lean` and `MemoryProgress.lean`, as in both monotonicity files and the
memory refinement files (semantics-refinement.md). Deriving the set-monad
theorems from the state-layer ones is one later refactor over fuel
monotonicity, progress and refinement together, tracked by #294. Rejected:
deriving them for progress alone now, which would move the path calculus below
`Calls.lean` and leave the three theorems following two patterns.

## Calls and fuel

A call has no op-level rule. Its meaning is its callee's run. A dialect names
the function that an op calls through `DialectCall` (`callee?`). The interpreter
runs that op, not its `denote`. It finds the callee in the module by symbol and
passes the op's operands as arguments. It binds the callee's returned values to
the op's results. A run belongs to a module: `Func.runOps` and `Func.run` take
the module whose functions calls run. The call effect is the run's, and it is
not a class constraint on the monad, so the tree of choices needs no node for
it (ADR-2026-10-29-2009). Rejected: a call effect as a class on the monad, like
`MonadChoice`, since the set monad has no module and `denote` cannot see the
budget.

`call` has no entry in `Core.Op.denote?`, so its `denote` has no outcome in the
set monad. The interpreter never reaches it. Where the spec counts which ops
have rules, an op with a callee has them. A statement proved op by op must leave
out the ops with a callee. M2's rewrite rules need the same exclusion, tracked
by #96 (ADR-2026-10-29-2006).

Fuel stays the interpreter's argument, not state in the monad. Every op takes
one step, a call included. `Func.runOps` returns the steps it leaves with the
values it returns. A callee gets the steps its caller has left after the call's
step. The caller goes on with the steps that the callee gives back. A callee
that runs out of fuel ends the run so. Its UB and stuck paths are its caller's
(ADR-2026-10-29-2009). The human ruled on 2026-11-02 (#70) that this interface,
a callee that receives the budget and gives back the rest, is designed before
`FuelMonotone`, `Progress` and `NeverStuck` are proved. Rejected: fuel in a
state monad, which makes fuel monotonicity a fact about the wrong counter; an
op step that takes the budget, so that each dialect counts fuel itself; and a
machine with a stack of frames, whose callee steps are no longer a run of the
callee.

The recursion is well-founded on the budget, not structural. Nothing is
`partial`. Fuel is a device of the Lean definitions. It must not change what a
program means, nor any result of `fir-ref`. Fuel monotonicity holds for every
function of every module, calls included, since only the interpreter counts
fuel (ADR-2026-10-29-2009). For a function that reaches an op without rules
it holds only vacuously on the paths that reach the op
([fir-ref.md](fir-ref.md#an-op-without-rules)). A run leaves at most its budget
(`Func.runOps_left_le`), and the definition goes on with `min k n`, which is
`k`, so that Lean sees the budget shrink. Lean makes `Func.runOps` irreducible:
proofs unfold it with its equation lemmas (`simp only [Func.runOps]`) and use
strong induction on the budget (`Nat.strongRecOn`), and `rfl` does not evaluate
a run without `unseal Func.runOps`.

## Stuck paths

A terminator may have results in the generic spec, but a run never binds them.
Validation has no rule that a terminator has no results, and `Exit` carries no
values. So "a terminator that jumps gives no results" is a condition that each
dialect meets for its own terminators, as half of the `jumps` field of
`Func.Local` and `Func.InModule`, in `lean/Fir/Execution/Jumps.lean` and
`Calls.lean`. Validation does not check it (ADR-2026-11-02-2248).

The generic progress and no-stuck theorems cover a function only through that
condition: `Func.neverStuck_of_local` and `Func.progress_of_local` ask it
through `Func.Local`, and `Func.neverStuck_of_inModule` and
`Func.progress_of_inModule` through `Func.InModule`. A function with a
terminator that may jump and has results cannot meet them, so the theorems say
nothing of it. So "a validated module never gets stuck" holds only for a dialect
whose terminators meet it. The core dialect meets it (`Core.Op.exit_goto`). No
path of a run of a function of a valid core module is stuck (`Core.neverStuck`).
`Exit` does not grow in M0. M4's design of exceptions and unwinding chooses
between a validation rule and values on `Exit`, and edits ADR-2026-11-02-2248
in place (ADR-2026-11-02-2248). The human ruled this on 2026-11-02 (#89,
option c). Rejected: a generic validation rule that a terminator has no
results, which forbids an `invoke`-style terminator whose result is defined on
one successor; and values on `Exit`, which changes `DialectDenote.exit`, the
run and likely the scope rule, in a shape that depends on how unwinding is
modelled.

`fir-ref run` walks a machine with explicit call frames. The machine is proved
equal to the spec's interpreter
([fir-ref-fast-paths.md](fir-ref-fast-paths.md#running)).

## Bit-vector proofs

The core law files have no use for `bv_decide` today. `bitVec_one_cases`, which
the core's round trip rests on, is proved by `revert v; decide`. The two proofs
at symbolic width, `divEv_zero_one`'s side goals and `shiftValues_msb`, stay as
they are, because `bv_decide` needs a width that is a literal. `bv_decide`
remains the tool that the roadmap names as the bar for admitting rewrite rules.
Rejected: `bv_decide` for `bitVec_one_cases`, which adds a native axiom under
the core round trip and trusts the compiler for a fact with two cases.
