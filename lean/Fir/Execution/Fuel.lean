import Fir.Execution.Behaviour

/-!
# Fuel and progress

Three obligations tie the interpreter's runs to the behaviours above. #10
defines the run of each function of a module on each argument vector of its
parameter types (`Func.runs`, and `Core.funcRuns` for the core dialect).
All three hold for every function of every valid core module, on every
argument vector, calls, recursion, branches and loops included:
`Core.fuelMonotone`, `Core.progress` and `Core.neverStuck`. #10 proved
them first for its tracer subset, `const`, `add` without flags and `ret`:
`Core.tracer_fuelMonotone`, `Core.tracer_progress` and
`Core.tracer_neverStuck`; then they were proved for every valid core
function that has no `call` op: `Core.callFree_fuelMonotone`,
`Core.callFree_progress` and `Core.callFree_neverStuck`.

* _Fuel monotonicity_ (`FuelMonotone`). More fuel never changes how a run
  that returns or hits UB ends. A return or UB that a run reaches at some
  budget, it reaches at every larger budget. One that it reaches at a larger
  budget, it reaches at a smaller one too, unless it can run out of fuel
  there. Then the observable behaviour does not depend on how the
  interpreter counts fuel, and refinement between two functions does not
  depend on how many steps each takes.
* _Progress_ (`Progress`). At every budget, a run has some outcome. An
  empty behaviour refines every source (see the next section), so a run
  with no outcome at all would pass for a correct one. Progress rules out
  only that: a run that has an outcome on one path may still lose others.
* _No stuck path_ (`NeverStuck`). No path of a run is stuck, at any budget.
  Which paths get stuck can depend on choices, so a run could be stuck on
  some paths and have outcomes on others. Those paths would be missing from
  its behaviour, and a behaviour with fewer outcomes refines more sources.
  With this obligation, with every op total (`OpTotal`, in the poison
  classes section), and with an interpreter whose own steps never drop a
  path, which #10's definition must ensure, every path of a valid
  function's run ends in an outcome.

The proofs are general. Fuel monotonicity holds for every function of every
module, of every dialect, calls included, whatever its ops do
(`Func.fuelMonotone`): only the interpreter counts fuel, and a callee gives
back to its caller the steps it leaves (ADR-2026-11-02-0836). Of a function
that reaches an op without rules it holds only vacuously on the paths that
reach the op, and says nothing of how such a function behaves
(ADR-2026-10-30-1855).

Progress and the no-stuck obligation hold for every valid function that
runs within itself (`Func.Local`): no op calls a function, a terminator
that jumps names a successor that it has and gives no results, and a
terminator that returns returns values of the function's result types. Its
run may jump and loop. No path of it is stuck (`Func.neverStuck_of_local`),
and when its ops are total it has an outcome at every budget
(`Func.progress_of_local`). A valid core function without a `call` op runs
within itself, and its ops are total, as every core op but `call` is. So
both hold for every valid core function without a `call` op.

With calls, they hold for every function of a module whose functions are
all valid and run within the module (`Func.InModule`): their terminators
keep to the rules above, and each call names a function of the module of
the call's type. A run may then call any function of the module, itself
included, as deep as its fuel allows (`Func.neverStuck_of_inModule`,
`Func.progress_of_inModule`). Every function of a valid core module runs
within the module, and every core op is total, `call` by its stand-in,
which the interpreter never runs. So both hold for every function of
every valid core module (`Core.progress`, `Core.neverStuck`). They are
statements about the run in the set monad, choices included, and
`fir-ref`'s modes report only what that run does (`Core.exhaustive_stuck`,
`Core.scripted_stuck`, `Core.sampled_stuck`), so no mode reports a stuck
path of such a function.
-/

namespace Fir

/-- More fuel never changes how a run that returns or hits UB ends. -/
structure FuelMonotone (run : Nat → Run O) : Prop where
  /-- A return or UB stays when the budget grows. -/
  up : ∀ {n m : Nat} {o : Outcome O}, n ≤ m → o ≠ .fuelExhausted →
    (run n).outcomes o → (run m).outcomes o
  /-- A return or UB at a larger budget is there at a smaller one, unless
  the smaller one can run out of fuel. -/
  down : ∀ {n m : Nat} {o : Outcome O}, n ≤ m → o ≠ .fuelExhausted →
    (run m).outcomes o → (run n).outcomes o ∨ (run n).outcomes .fuelExhausted

/-- At every budget, the run has some outcome. -/
def Progress (run : Nat → Run O) : Prop :=
  ∀ n, ∃ o, (run n).outcomes o

/-- At every budget, no path of the run is stuck. -/
def NeverStuck (run : Nat → Run O) : Prop :=
  ∀ n, ¬ (run n).IsStuck

/--
The bridge lemma. At a budget `N` at which a fuel-monotone run cannot run out
of fuel, the outcomes of that one run are exactly the observable behaviour.
This is what lets a harness judge a function by its runs at one budget.
-/
theorem observable_eq_at {run : Nat → Run O} (hm : FuelMonotone run) {N : Nat}
    (hN : ¬ (run N).outcomes .fuelExhausted) (t : Outcome O) :
    observable run t ↔ (run N).outcomes t := by
  have final : ∀ {o : Outcome O}, o ≠ .fuelExhausted →
      ((∃ n, (run n).outcomes o) ↔ (run N).outcomes o) := fun ho =>
    ⟨fun ⟨n, hn⟩ => (Nat.le_total n N).elim (fun h => hm.up h ho hn)
        (fun h => (hm.down h ho hn).resolve_right hN),
      fun h => ⟨N, h⟩⟩
  cases t with
  | ret o => exact final (fun h => nomatch h)
  | ub r => exact final (fun h => nomatch h)
  | fuelExhausted => exact ⟨fun h => absurd (h N) hN, fun h => absurd h hN⟩

/-- With progress, a run's observable behaviour has some outcome. -/
theorem observable_nonempty {run : Nat → Run O} (hp : Progress run) :
    ∃ t, observable run t := by
  by_cases h : ∀ n, (run n).outcomes .fuelExhausted
  · exact ⟨.fuelExhausted, h⟩
  · obtain ⟨n, hn⟩ := Classical.not_forall.mp h
    obtain ⟨t, ht⟩ := hp n
    cases t with
    | ret o => exact ⟨.ret o, n, ht⟩
    | ub r => exact ⟨.ub r, n, ht⟩
    | fuelExhausted => exact absurd ht hn

end Fir
