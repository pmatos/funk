import Fir.Execution.NaNModes
import Fir.Execution.TraceDialect

/-!
# Modes that see the end of a return

`fir-ref run` reports how a run ends as an observer sees it
(ADR-2026-11-09-1540): at a return, the returned values, the allocations
that escaped and the memory reachable from them, the end of the return
(`Fir.Execution.ObserveEnd`). The tree that the modes walk with memory drops
the memories at the end of each path (the section on modes with memory). The
tree here keeps them: each return is seen at its end, with the memories at
the end of the path, after the function's frame has been left, and nothing
escaped. It is the tree of the runs with memory, each return seen at its
end, that a dialect whose ops show no event has as its traced runs
(`Func.memEndRuns`, `Func.traceObservable_traceRuns`).

So exhaustive mode on this tree, within its budget, gives exactly the
outcomes of those runs, scripted mode on a sequence that fits gives one of
them, and so does the walk that tries a few NaNs, all of them when no path
made a NaN choice. For a dialect whose ops show no event, a return or UB
that a mode reports is an outcome of the function's traced runs, with an
empty trace.
-/

namespace Fir

open Memory

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  {N : Type} [DecidableEq N] {ε : Type}

/-- The tree of a run with memory of the function `f` of the module `M`, on
`args` with `fuel` steps, each return seen at its end: its run in the state
layer over the tree of choices, from the empty memories, a return of the
values `v` with the memories `S` at the end of its path seen as the end
`⟨v, S, []⟩`, where the memory numbered `n` is `μ n` and addresses are
compared by `ar`. -/
def Func.memEndTree (unit : N → Nat) (μ : Nat → N) (ar : AddrRule)
    [DialectDenote d (StateT (Memories N unit) (ChoiceTree ε))] (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    ChoiceTree ε (Except Stuck (Result (End unit μ ar (List (DVal d))))) :=
  (fun p => (TraceState.mk p.2 []).endOf μ ar p.1) <$>
    (f.run M (m := StateT (Memories N unit) (ChoiceTree ε)) args fuel).run.run Memories.empty

variable [DialectEffects d] [DialectMemDenote d] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem d → N) (L : RunItems) (μ : Nat → N) (ar : AddrRule)
  [DialectDenote d (StateT (Memories N (unitsOf lay)) (ChoiceTree ε))]

/-- The tree of a run with memory, each return seen at its end, has as its
set the run with memory, each return seen at its end, when the semantics in
the layer over the tree denotes the semantics with memory. -/
theorem Func.memEndTree_toSet (h : MemMapsDenote (d := d) lay (ε := ε) ρ L) (M : Module d)
    (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    (f.memEndTree (unitsOf lay) (ε := ε) μ ar M args fuel).toSet =
      f.memEndRuns lay ρ L μ ar M args fuel := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ L
  show ChoiceTree.toSet (_ <$> _) = Functor.map (f := SetM) _
    ((f.run M (m := StateT (Memories N (unitsOf lay)) SetM) args fuel).run.run Memories.empty)
  rw [← Func.run_toSetState h M f args fuel]
  exact ChoiceTree.toSetMorphism.map_map _ _

/-- Exhaustive mode on the tree that sees each return at its end, within
its choice budget, gives exactly the outcomes of the run with memory, each
return seen at its end, at the fuel budget it runs with. -/
theorem Func.memEndExplore_outcomes (h : MemMapsDenote (d := d) lay (ε := ε) ρ L) (M : Module d)
    (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat)
    {ls : List (ChoiceTree.Leaf ε (Except Stuck (Result (End (unitsOf lay) μ ar
      (List (DVal d))))) × Nat)}
    (hx : (f.memEndTree (unitsOf lay) μ ar M args fuel).explore budget = some ls)
    (o : Outcome (End (unitsOf lay) μ ar (List (DVal d)))) :
    Run.outcomes (f.memEndRuns lay ρ L μ ar M args fuel) o ↔
      ∃ p ∈ ls, p.1.pathEnd = .outcome o := by
  rw [Run.outcomes_iff, ← Func.memEndTree_toSet lay ρ L μ ar h, ChoiceTree.explore_toSet hx]
  simp only [ChoiceTree.Leaf.ev?_eq_outcome]

/-- Scripted mode on the tree that sees each return at its end, on a choice
sequence that fits, gives an outcome of the run with memory, each return
seen at its end. -/
theorem Func.memEndScript_outcomes (h : MemMapsDenote (d := d) lay (ε := ε) ρ L) {σ : Type}
    (read : (w : Nat) → σ → Option (BitVec w)) (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ)
    {l : ChoiceTree.Leaf ε (Except Stuck (Result (End (unitsOf lay) μ ar (List (DVal d)))))}
    {c : Nat} (hs : (f.memEndTree (unitsOf lay) μ ar M args fuel).script read cs 0 = .ok (l, c))
    {o : Outcome (End (unitsOf lay) μ ar (List (DVal d)))} (ho : l.pathEnd = .outcome o) :
    Run.outcomes (f.memEndRuns lay ρ L μ ar M args fuel) o := by
  rw [Run.outcomes_iff, ← Func.memEndTree_toSet lay ρ L μ ar h]
  exact ChoiceTree.script_toSet hs ((ChoiceTree.Leaf.ev?_eq_outcome l o).2 ho)

/-- Each outcome that the walk that tries a few NaNs lists on the tree that
sees each return at its end is an outcome of the run with memory, each
return seen at its end; and when no path it lists made a NaN choice, it
lists all of them. -/
theorem Func.memEndExploreNaN_outcomes (h : MemMapsDenote (d := d) lay (ε := ε) ρ L)
    (M : Module d) (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat)
    (nans : List Nat)
    {ls : List (ChoiceTree.Leaf ε (Except Stuck (Result (End (unitsOf lay) μ ar
      (List (DVal d))))) × Nat × Nat)}
    (hx : (f.memEndTree (unitsOf lay) μ ar M args fuel).exploreNaN nans budget = some ls)
    (o : Outcome (End (unitsOf lay) μ ar (List (DVal d)))) :
    ((∃ p ∈ ls, p.1.pathEnd = .outcome o) → Run.outcomes (f.memEndRuns lay ρ L μ ar M args fuel) o) ∧
      ((∀ p ∈ ls, p.2.2 = 0) →
        Run.outcomes (f.memEndRuns lay ρ L μ ar M args fuel) o → ∃ p ∈ ls, p.1.pathEnd = .outcome o) := by
  rw [Run.outcomes_iff, ← Func.memEndTree_toSet lay ρ L μ ar h]
  refine ⟨fun ⟨p, hp, ho⟩ =>
    ChoiceTree.exploreNaN_sub hx p hp _ ((ChoiceTree.Leaf.ev?_eq_outcome p.1 o).2 ho), fun h0 => ?_⟩
  rw [ChoiceTree.exploreNaN_toSet hx h0]
  simp only [ChoiceTree.Leaf.ev?_eq_outcome]
  exact id

/-- For a dialect whose ops show no event, a return or UB of the run with
memory at some fuel budget, each return seen at its end, is an outcome of
the function's traced runs, with an empty trace. -/
theorem Func.traceObservable_of_memEnd [DialectTrace d] [LiftsMem d] (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) {fuel : Nat}
    {o : Outcome (End (unitsOf lay) μ ar (List (DVal d)))} (ho : o ≠ .fuelExhausted)
    (h : Run.outcomes (f.memEndRuns lay ρ L μ ar M args fuel) o) :
    traceObservable (f.traceRuns lay ρ L μ ar M args) (.ofOutcome o) := by
  rw [Func.traceObservable_traceRuns]
  refine ⟨o, ?_, rfl⟩
  cases o with
  | ret e => exact ⟨fuel, h⟩
  | ub r => exact ⟨fuel, h⟩
  | fuelExhausted => exact absurd rfl ho

end Fir
