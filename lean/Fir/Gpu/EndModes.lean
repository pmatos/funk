import Fir.Gpu.Modes
import Fir.Gpu.Trace
import Fir.Execution.MemoryEndModes

/-!
# The modes of the core and `gpu` that see the end of a return

`fir-ref run` reports, for a run of a function of the sum of the core and
`gpu` at a work-item, how each path ends as an observer sees it: at a
return, its end (ADR-2026-11-09-1540). Its modes walk the tree of the run
with memory that sees each return at its end, the spec's
(`Func.memEndTree`), as the modes of the core and `gpu` walk the tree that
sees a return as its values: from the empty memories, each memory with its
entry in the module's data layout, named by its number. The end of a
return compares no addresses (`ObservedEnd`), and the memory numbered `n`
is the memory `n` of the run.

Within its budget, exhaustive mode gives exactly the outcomes of the run
with memory, each return seen at its end; scripted and sampled modes give
one of them, and so does the walk that tries a few NaNs, all of them when
no path made a NaN choice. Neither the core nor `gpu` shows an event yet,
so a return or UB that a mode reports is an outcome of the spec's traced
runs of the function (`Func.observedRuns`), with an empty trace.
-/

namespace Fir.Gpu

open Memory

variable [WorkItem]

/-- How a return is seen at its end, in a run of a function of the module
`M`: the end compares no addresses, and the memory numbered `n` is the
memory `n` of the run. -/
abbrev RunEnd (M : Module CoreGpu) : Type :=
  ObservedEnd (unitsOf M.layout.entry) id (List (DVal CoreGpu))

/-- A leaf of the tree that the modes walk when they see each return at its
end. -/
abbrev EndLeaf (M : Module CoreGpu) := ChoiceTree.Leaf Core.Op (Except Stuck (Result (RunEnd M)))

/-- The tree of a run with memory of the function `f` of the module `M` at
the work-item, on `args` with `fuel` steps, each return seen at its end:
from the empty memories, each memory with its entry in `M`'s data layout,
named by its number. -/
def endTree (M : Module CoreGpu) (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) : ChoiceTree Core.Op (Except Stuck (Result (RunEnd M))) :=
  letI := memTreeDenote M.layout.entry memName M.runItems
  f.memEndTree (unitsOf M.layout.entry) id AddrRule.ignore M args fuel

/-- Exhaustive mode on the function `f` of the module `M` at the work-item,
each return seen at its end. -/
def exhaustiveEnd (M : Module CoreGpu) (f : Func CoreGpu)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) :
    Option (List (EndLeaf M × Nat)) :=
  (endTree M f args fuel).explore budget

/-- The walk that tries a few NaNs on the function `f` of the module `M` at
the work-item, each return seen at its end. -/
def exhaustiveNaNEnd (M : Module CoreGpu) (f : Func CoreGpu)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) (nans : List Nat) :
    Option (List (EndLeaf M × Nat × Nat)) :=
  (endTree M f args fuel).exploreNaN nans budget

/-- Scripted mode on the function `f` of the module `M` at the work-item,
each return seen at its end. -/
def scriptedEnd {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (M : Module CoreGpu)
    (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ) :
    Except (ChoiceTree.Misfit σ) (EndLeaf M × Nat) :=
  (endTree M f args fuel).script read cs 0

/-- Sampled mode on the function `f` of the module `M` at the work-item,
each return seen at its end. -/
def sampledEnd {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (M : Module CoreGpu)
    (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    EndLeaf M × List ChoiceTree.Chosen :=
  (endTree M f args fuel).sample draw g

/-! # Outcomes of the runs with memory, each return seen at its end -/

/-- Exhaustive mode, within its choice budget, gives exactly the outcomes of
the run with memory, each return seen at its end. -/
theorem exhaustiveEnd_memOutcomes (M : Module CoreGpu) (f : Func CoreGpu)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) {ls : List (EndLeaf M × Nat)}
    (hx : exhaustiveEnd M f args fuel budget = some ls) (o : Outcome (RunEnd M)) :
    Run.outcomes (f.memEndRuns M.layout.entry memName M.runItems id AddrRule.ignore M args fuel) o ↔
      ∃ p ∈ ls, p.1.pathEnd = .outcome o :=
  letI := memTreeDenote M.layout.entry memName M.runItems
  Func.memEndExplore_outcomes M.layout.entry memName M.runItems id AddrRule.ignore
    (memMapsDenote M.layout.entry memName M.runItems) M f args fuel budget hx o

/-- Each outcome that the walk that tries a few NaNs lists is an outcome of
the run with memory, each return seen at its end; and when no path it lists
made a NaN choice, it lists all of them. -/
theorem exhaustiveNaNEnd_memOutcomes (M : Module CoreGpu) (f : Func CoreGpu)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) (nans : List Nat)
    {ls : List (EndLeaf M × Nat × Nat)} (hx : exhaustiveNaNEnd M f args fuel budget nans = some ls)
    (o : Outcome (RunEnd M)) :
    ((∃ p ∈ ls, p.1.pathEnd = .outcome o) →
      Run.outcomes (f.memEndRuns M.layout.entry memName M.runItems id AddrRule.ignore M args fuel) o) ∧
    ((∀ p ∈ ls, p.2.2 = 0) →
      Run.outcomes (f.memEndRuns M.layout.entry memName M.runItems id AddrRule.ignore M args fuel) o →
        ∃ p ∈ ls, p.1.pathEnd = .outcome o) :=
  letI := memTreeDenote M.layout.entry memName M.runItems
  Func.memEndExploreNaN_outcomes M.layout.entry memName M.runItems id AddrRule.ignore
    (memMapsDenote M.layout.entry memName M.runItems) M f args fuel budget nans hx o

/-- Scripted mode, on a choice sequence that fits, gives an outcome of the
run with memory, each return seen at its end. -/
theorem scriptedEnd_memOutcomes {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (M : Module CoreGpu) (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (cs : List σ) {l : EndLeaf M} {c : Nat}
    (hs : scriptedEnd read M f args fuel cs = .ok (l, c)) {o : Outcome (RunEnd M)}
    (ho : l.pathEnd = .outcome o) :
    Run.outcomes (f.memEndRuns M.layout.entry memName M.runItems id AddrRule.ignore M args fuel) o :=
  letI := memTreeDenote M.layout.entry memName M.runItems
  Func.memEndScript_outcomes M.layout.entry memName M.runItems id AddrRule.ignore
    (memMapsDenote M.layout.entry memName M.runItems) read M f args fuel cs hs ho

/-- Sampled mode gives an outcome of the run with memory, each return seen
at its end, whatever the generator: the values it chose are a choice
sequence that fits the run, on which scripted mode reports the same
path. -/
theorem sampledEnd_memOutcomes {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (M : Module CoreGpu) (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (g : γ) {o : Outcome (RunEnd M)}
    (ho : (sampledEnd draw M f args fuel g).1.pathEnd = .outcome o) :
    Run.outcomes (f.memEndRuns M.layout.entry memName M.runItems id AddrRule.ignore M args fuel) o := by
  have h := ChoiceTree.sample_script (draw := draw) (endTree M f args fuel) g 0
  rw [Nat.zero_add] at h
  exact scriptedEnd_memOutcomes _ M f args fuel _ h ho

/-- A return or UB of the run with memory at some fuel budget, each return
seen at its end, is an outcome of the spec's traced runs of the function,
with an empty trace: neither the core nor `gpu` shows an event. -/
theorem observedRuns_of_memEnd (M : Module CoreGpu) (f : Func CoreGpu)
    (args : HVector toType (f.params.map (·.2))) {fuel : Nat} {o : Outcome (RunEnd M)}
    (ho : o ≠ .fuelExhausted)
    (h : Run.outcomes (f.memEndRuns M.layout.entry memName M.runItems id AddrRule.ignore M args
      fuel) o) :
    traceObservable (f.observedRuns M.layout.entry memName M.runItems id M args) (.ofOutcome o) :=
  Func.traceObservable_of_memEnd M.layout.entry memName M.runItems id AddrRule.ignore M f args ho h

end Fir.Gpu
