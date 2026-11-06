import Fir.Execution.Behaviour

/-!
# Fuel and progress

Three obligations tie the interpreter's runs to the behaviours above. The
run of each function of a module, on each argument vector of its parameter
types, is defined in the section "The runs of a function, and fuel
monotonicity". All three obligations hold for every function of every
valid core module, on every argument vector, calls, recursion, branches
and loops included. The
section on core functions without calls proves them for a function with no
`call` op, and the section on core functions with calls for all of them.

* _Fuel monotonicity_: more fuel never changes how a run that returns or
  hits UB ends.
* _Progress_: at every budget, a run has some outcome.
* _No stuck path_: no path of a run is stuck, at any budget.

Each is defined below, with why it is needed. With no stuck path, with
every op that runs by its own rule total (the totality obligation, in the
section on poison classes), and with an interpreter whose own steps never
drop a path, as the section on the interpreter explains, every path of a
valid function's run ends in an outcome.

The proofs are general. Fuel monotonicity holds for every function of every
module, of every dialect, calls included, whatever its ops do (the section
"The runs of a function, and fuel monotonicity"): only the interpreter
counts fuel, and a callee gives back to its caller the steps it leaves
(ADR-2026-11-02-0836). For a function that reaches an op to which its
dialect gives no execution rule (ADR-2026-10-30-1855), fuel monotonicity
holds only vacuously on the paths that reach that op, and says nothing
about how the function behaves there.

Progress and the no-stuck obligation hold for every valid function that
runs within itself: no op calls a function, a terminator that jumps names
a successor that it has and gives no results, and a terminator that
returns returns values of the function's result types. Its run may jump and
loop. No path of it is stuck, and when its ops are total it has an outcome
at every budget (the section on progress with jumps and loops). A valid
core function without a `call` op runs within itself, and its ops are
total, as every core op but `call` is. So both hold for every valid core
function without a `call` op.

With calls, they hold for every function of a module whose functions are
all valid and run within the module: their terminators keep to the rules
above, and each call names a function of the module of the call's type. A
run may then call any function of the module, itself included, as deep as
its fuel allows (the section on progress with calls), when every terminator
and every op with no callee is total: an op with a callee goes on by its
callee's run, and needs no rule of its own (ADR-2026-11-02-1514). Every
function of a valid core module runs within the module, and every core op
but `call` is total. So both hold for every function of every valid core
module. They are statements about the run in the set monad, choices
included, and `fir-ref`'s modes report only what that run does (the section
on the core dialect's modes), so no mode reports a stuck path of such a
function.
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
  classical
  by_cases h : ∀ n, (run n).outcomes .fuelExhausted
  · exact ⟨.fuelExhausted, h⟩
  · obtain ⟨n, hn⟩ := Classical.not_forall.mp h
    obtain ⟨t, ht⟩ := hp n
    cases t with
    | ret o => exact ⟨.ret o, n, ht⟩
    | ub r => exact ⟨.ub r, n, ht⟩
    | fuelExhausted => exact absurd ht hn

end Fir
