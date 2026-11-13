import Fir.Core.TreeRules

/-!
# The core dialect's exhaustive, scripted and sampled runs

The modes run the core dialect with memory (the section on modes with
memory): its rules with memory in the state layer over the tree of choices
(the section on the core dialect in the tree of choices), from the empty
memories. A
mode runs a module with its own layout: each memory of the run has its
entry in the module's data layout, which gives its unit, its byte order and
the width of its pointers, and the run names the core's memories by
themselves, by their numbers. So the
theorems of exhaustive and scripted modes hold of the runs with memory of
every core function, on every argument vector, at every fuel budget; and
since the core's runs with memory are its runs, they hold of its runs in
the set monad too. `fir-ref` computes the exhaustive, scripted and sampled
modes defined below, and nothing else, to report a run. The values that
sampled mode chose fit the run, so it inherits scripted mode's theorems.

The theorems hold on every argument vector of the function's parameter types,
poison included, and `fir-ref run` takes `poison` as an argument of any `iN`. A
run on a poison argument is refined by the run with any value in its place,
calls and recursion included, as the section on refinement through core calls
proves. So the differential test harness, which checks compiled code against
`fir-ref`, runs native code, which holds no poison, on poison stand-ins in
place of each poison argument, and judges each result against the outcomes that
`fir-ref` lists for the run on the poison
(`docs/decisions/fir-ref.md#poison-arguments`).
-/

namespace Fir.Core

open Memory

/-- The tree of a run with memory of the core function `f` of the module
`M`, on `args` with `fuel` steps, that the modes walk: from the empty
memories, each memory with its entry in `M`'s data layout, and the core's
memories named by themselves, by their numbers. -/
def modeTree (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    ChoiceTree Op (Except Stuck (Result Obs)) :=
  letI := memTreeDenote M.layout.entry id
  f.memTree (unitsOf M.layout.entry) M args fuel

/-- Exhaustive mode on the core function `f` of the module `M`: every path
of its run with memory on `args` with `fuel` steps, from the empty memories,
each with its entry in `M`'s data layout, when no path chooses more than
`budget` bits in all. -/
def exhaustive (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) :
    Option (List (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat)) :=
  (modeTree M f args fuel).explore budget

/-- Scripted mode on the core function `f` of the module `M`: the path of
its run with memory on `args` with `fuel` steps, from the empty memories,
that the choice sequence `cs` names, each value read by `read`, or why `cs`
does not fit the run. -/
def scripted {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (M : Module CoreDialect)
    (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ) :
    Except (ChoiceTree.Misfit σ) (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat) :=
  (modeTree M f args fuel).script read cs 0

/-- Sampled mode on the core function `f` of the module `M`: the path of
its run with memory on `args` with `fuel` steps, from the empty memories, on
which `draw` gives each choice, from the generator `g`, and the values
chosen on it. -/
def sampled {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (M : Module CoreDialect)
    (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × List ChoiceTree.Chosen :=
  (modeTree M f args fuel).sample draw g

/-! # Outcomes of the runs with memory

The modes run a module with its own layout: each theorem speaks of the runs
with memory of a core function where each memory of the run has its entry
in the module's data layout, and the run names the core's memories by
themselves. -/

/-- Exhaustive mode, within its choice budget, gives exactly the outcomes
of the run with memory at the fuel budget it runs with. -/
theorem exhaustive_memOutcomes (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat)
    {ls : List (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat)}
    (hx : exhaustive M f args fuel budget = some ls) (o : Outcome Obs) :
    Run.outcomes (f.memRuns M.layout.entry id M args fuel) o ↔ ∃ p ∈ ls, p.1.pathEnd = .outcome o :=
  letI := memTreeDenote M.layout.entry id
  Func.memExplore_outcomes M.layout.entry id (memMapsDenote M.layout.entry id) M f args fuel
      budget hx o

/-- Exhaustive mode, within its choice budget, lists a stuck path exactly
when the run with memory has one. -/
theorem exhaustive_memStuck (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat)
    {ls : List (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat)}
    (hx : exhaustive M f args fuel budget = some ls) :
    Run.IsStuck (f.memRuns M.layout.entry id M args fuel) ↔
      ∃ p ∈ ls, ∃ st, p.1.pathEnd = .stuck st :=
  letI := memTreeDenote M.layout.entry id
  Func.memExplore_stuck M.layout.entry id (memMapsDenote M.layout.entry id) M f args fuel budget hx

/-- Scripted mode, on a choice sequence that fits, gives an outcome of the
run with memory at the fuel budget it runs with. -/
theorem scripted_memOutcomes {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (cs : List σ) {l : ChoiceTree.Leaf Op (Except Stuck (Result Obs))} {c : Nat}
    (hs : scripted read M f args fuel cs = .ok (l, c)) {o : Outcome Obs}
    (ho : l.pathEnd = .outcome o) : Run.outcomes (f.memRuns M.layout.entry id M args fuel) o :=
  letI := memTreeDenote M.layout.entry id
  Func.memScript_outcomes M.layout.entry id (memMapsDenote M.layout.entry id) read M f args fuel
      cs hs ho

/-- Scripted mode, on a choice sequence that fits, reports a stuck path
only when the run with memory has one. -/
theorem scripted_memStuck {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (cs : List σ) {l : ChoiceTree.Leaf Op (Except Stuck (Result Obs))} {c : Nat}
    (hs : scripted read M f args fuel cs = .ok (l, c)) {st : Stuck}
    (hst : l.pathEnd = .stuck st) : Run.IsStuck (f.memRuns M.layout.entry id M args fuel) :=
  letI := memTreeDenote M.layout.entry id
  Func.memScript_stuck M.layout.entry id (memMapsDenote M.layout.entry id) read M f args fuel cs
      hs hst

/-- The values that sampled mode chose are a choice sequence that fits the
run: scripted mode on them reports the same path, with as many choices. -/
theorem sampled_fits {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (M : Module CoreDialect)
    (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    scripted ChoiceTree.readChosen M f args fuel (sampled draw M f args fuel g).2 =
      .ok ((sampled draw M f args fuel g).1,
        (sampled draw M f args fuel g).2.length) := by
  have h := ChoiceTree.sample_script (draw := draw) (modeTree M f args fuel) g 0
  rw [Nat.zero_add] at h
  exact h

/-- Sampled mode gives an outcome of the run with memory at the fuel budget
it runs with, whatever the generator. -/
theorem sampled_memOutcomes {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (g : γ) {o : Outcome Obs}
    (ho : (sampled draw M f args fuel g).1.pathEnd = .outcome o) :
    Run.outcomes (f.memRuns M.layout.entry id M args fuel) o :=
  scripted_memOutcomes _ M f args fuel _ (sampled_fits draw M f args fuel g) ho

/-- Sampled mode reports a stuck path only when the run with memory has
one. -/
theorem sampled_memStuck {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (g : γ) {st : Stuck}
    (hst : (sampled draw M f args fuel g).1.pathEnd = .stuck st) :
    Run.IsStuck (f.memRuns M.layout.entry id M args fuel) :=
  scripted_memStuck _ M f args fuel _ (sampled_fits draw M f args fuel g) hst

/-! # Outcomes of the runs

The core's ops touch no memory, so the tree of a core run with memory is the
tree of its run with no memory: the modes report what they reported before
memory, path for path, and each mode's theorems speak of the run in the set
monad too. -/

/-- The tree that the modes walk is the tree of the run: each core op keeps
the memories, so the paths, their choices and how each ends are the same,
and only the memories that the tree drops at each leaf differ. -/
theorem memTree_eq (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    modeTree M f args fuel = (f.run M (m := ChoiceTree Op) args fuel).run := by
  letI := memTreeDenote M.layout.entry id
  have h := Func.run_map (memTree_liftState M.layout.entry id)
    (MonadMorphism.liftState_mapsFrame (Mem := Nat) (unit := unitsOf M.layout.entry)
      (fun _ => rfl)) M f args fuel
  unfold modeTree Func.memTree
  rw [← h]
  show (ChoiceTree.bind _ fun a => .pure (a, Memories.empty)).bind (fun p => .pure p.1) = _
  rw [ChoiceTree.bind_assoc]
  exact ChoiceTree.bind_pure _

/-- Exhaustive mode, within its choice budget, gives exactly the outcomes
of the run at the fuel budget it runs with. -/
theorem exhaustive_outcomes (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat)
    {ls : List (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat)}
    (hx : exhaustive M f args fuel budget = some ls) (o : Outcome Obs) :
    Run.outcomes (f.run M (m := SetM) args fuel) o ↔ ∃ p ∈ ls, p.1.pathEnd = .outcome o := by
  rw [exhaustive, memTree_eq] at hx
  exact Func.explore_outcomes mapsDenote M f args fuel budget hx o

/-- Exhaustive mode, within its choice budget, lists a stuck path exactly
when the run has one. -/
theorem exhaustive_stuck (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat)
    {ls : List (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat)}
    (hx : exhaustive M f args fuel budget = some ls) :
    Run.IsStuck (f.run M (m := SetM) args fuel) ↔ ∃ p ∈ ls, ∃ st, p.1.pathEnd = .stuck st := by
  rw [exhaustive, memTree_eq] at hx
  exact Func.explore_stuck mapsDenote M f args fuel budget hx

/-- Scripted mode, on a choice sequence that fits, gives an outcome of the
run at the fuel budget it runs with. -/
theorem scripted_outcomes {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (cs : List σ) {l : ChoiceTree.Leaf Op (Except Stuck (Result Obs))} {c : Nat}
    (hs : scripted read M f args fuel cs = .ok (l, c)) {o : Outcome Obs}
    (ho : l.pathEnd = .outcome o) : Run.outcomes (f.run M (m := SetM) args fuel) o := by
  rw [scripted, memTree_eq] at hs
  exact Func.script_outcomes mapsDenote read M f args fuel cs hs ho

/-- Scripted mode, on a choice sequence that fits, reports a stuck path
only when the run has one. -/
theorem scripted_stuck {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (cs : List σ) {l : ChoiceTree.Leaf Op (Except Stuck (Result Obs))} {c : Nat}
    (hs : scripted read M f args fuel cs = .ok (l, c)) {st : Stuck}
    (hst : l.pathEnd = .stuck st) : Run.IsStuck (f.run M (m := SetM) args fuel) := by
  rw [scripted, memTree_eq] at hs
  exact Func.script_stuck mapsDenote read M f args fuel cs hs hst

/-- Sampled mode gives an outcome of the run at the fuel budget it runs
with, whatever the generator. -/
theorem sampled_outcomes {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (g : γ) {o : Outcome Obs}
    (ho : (sampled draw M f args fuel g).1.pathEnd = .outcome o) :
    Run.outcomes (f.run M (m := SetM) args fuel) o :=
  scripted_outcomes _ M f args fuel _ (sampled_fits draw M f args fuel g) ho

/-- Sampled mode reports a stuck path only when the run has one. -/
theorem sampled_stuck {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (g : γ) {st : Stuck}
    (hst : (sampled draw M f args fuel g).1.pathEnd = .stuck st) :
    Run.IsStuck (f.run M (m := SetM) args fuel) :=
  scripted_stuck _ M f args fuel _ (sampled_fits draw M f args fuel g) hst

end Fir.Core
