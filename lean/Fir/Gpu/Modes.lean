import Fir.Gpu.Runs
import Fir.Core.Modes
import Fir.Sum.RunLaws

/-!
# The exhaustive, scripted and sampled runs of the core and `gpu`

`fir-ref run` runs a function of the sum of the core and `gpu`, `CoreGpu`,
at a work-item, the run's input with its arguments: a function of the
module, or a kernel of one of its device modules, nested at any depth, in
the module of its table (`Module.nest`). The modes run it as they run the
core alone (the section on the core's modes): with memory, in the state
layer over the tree of choices, from the empty memories, each memory with
its entry in the module's data layout, which a nested table shares with
its host. The run names the sum's memories by the core's numbers
(`memName`): `gpu` has no memory of its own, so its names are the core's,
and work-group memory is the memory of the host's layout that an
allocation's result names.

A core op runs by its rule in the tree, and an op without rules ends its
path with no outcome, naming the core op; a question of `gpu` gives the
work-item's answer, and `gpu.work_group_alloca` allocates for the whole
run. Each side's semantics in the tree denotes its semantics
with memory, so the sum's does (`Dialect.sum.mapsDenote`), and the theorems
of exhaustive, scripted and sampled modes hold of the runs with memory of
every function of the sum, at every work-item, on every argument vector, at
every fuel budget.
-/

namespace Fir.Gpu

open Memory

/-- The run's name for each memory of the sum: the core's number, as `gpu`
names the core's memories and has none of its own. -/
def memName : DialectEffects.Mem CoreGpu → Nat
  | .inl n => n
  | .inr e => e.elim

variable [WorkItem]

/-- The rules of `gpu` in the state layer over the tree of choices, where a
run's memories have the layout entries `lay` and the run names `gpu`'s
memory `x` as `ρ x`: a question gives its results and keeps the memories,
and an allocation allocates. -/
@[instance_reducible] def treeDenote {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem GpuDialect → N) :
    DialectDenote GpuDialect (StateT (Memories N (unitsOf lay)) (ChoiceTree Core.Op)) :=
  memDenoteIn lay ρ

/-- The sum's semantics in the state layer over the tree of choices, where a
run's memories have the layout entries `lay` and the run names the sum's
memory `x` as `ρ x`: a core op runs by its rule with memory, an op with no
rule ends its path with no outcome, and an op of `gpu` by its rule. -/
@[instance_reducible] def memTreeDenote {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem CoreGpu → N) :
    DialectDenote CoreGpu (StateT (Memories N (unitsOf lay)) (ChoiceTree Core.Op)) :=
  letI := Core.memTreeDenote lay (ρ ∘ DialectMemOver.ofBase (base := CoreDialect) (e := GpuExt))
  letI := treeDenote lay ρ
  Dialect.sum.instDialectDenote

variable {N : Type} [DecidableEq N] (lay : N → MemLayout)

/-- The rules of `gpu` in the layer over the tree denote its semantics with
memory: `toSet` through the layer keeps a result, the memories and an
allocation. -/
theorem treeMapsDenote (ρ : DialectEffects.Mem GpuDialect → N) :
    letI := treeDenote lay ρ
    MemMapsDenote (d := GpuDialect) lay (ε := Core.Op) ρ :=
  @MonadMorphism.MapsDenote.mk _ _ _ _ (ChoiceTree.toSetState Core.Op (Memories N (unitsOf lay)))
    GpuDialect _ _ (treeDenote lay ρ) (DialectMemDenote.denoteAt (d := GpuDialect) lay ρ)
    (fun op _ => by
      cases op with
      | query => exact MonadMorphism.map_pure _ _
      | alloc t c a n =>
        show (ChoiceTree.toSetState Core.Op (Memories N (unitsOf lay))).map
            (allocRule (m := StateT _ (ChoiceTree Core.Op)) lay ρ t c a n) =
          allocRule (m := StateT (Memories N (unitsOf lay)) SetM) lay ρ t c a n
        unfold allocRule
        erw [MonadMorphism.map_map]
        exact congrArg _ (ChoiceTree.toSetMorphism.state_alloc (Mem := N) (unit := unitsOf lay) _ _ _ _))
    (fun _ _ => MonadMorphism.map_pure _ _)

/-- The sum's semantics in the layer over the tree denotes its semantics with
memory, wherever a run names the sum's memories, whatever their entries. -/
theorem memMapsDenote (ρ : DialectEffects.Mem CoreGpu → N) :
    letI := memTreeDenote lay ρ
    MemMapsDenote (d := CoreGpu) lay (ε := Core.Op) ρ :=
  @Dialect.sum.mapsDenote _ _ _ _ _ _ _ _ _ _ _
    (Core.memTreeDenote lay (ρ ∘ DialectMemOver.ofBase (base := CoreDialect) (e := GpuExt)))
    (DialectMemDenote.denoteAt (d := CoreDialect) lay
      (ρ ∘ DialectMemOver.ofBase (base := CoreDialect) (e := GpuExt)))
    (treeDenote lay ρ) (DialectMemDenote.denoteAt (d := GpuDialect) lay ρ)
    (Core.memMapsDenote lay (ρ ∘ DialectMemOver.ofBase (base := CoreDialect) (e := GpuExt)))
    (treeMapsDenote lay ρ)

/-- The tree of a run with memory of the function `f` of the module `M` at
the work-item, on `args` with `fuel` steps, that the modes walk: from the
empty memories, each memory with its entry in `M`'s data layout, named by
its number. -/
def modeTree (M : Module CoreGpu) (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) : ChoiceTree Core.Op (Except Stuck (Result (List (DVal CoreGpu)))) :=
  letI := memTreeDenote M.layout.entry memName
  f.memTree (unitsOf M.layout.entry) M args fuel

/-- A leaf of the tree that the modes walk. -/
abbrev Leaf := ChoiceTree.Leaf Core.Op (Except Stuck (Result (List (DVal CoreGpu))))

/-- Exhaustive mode on the function `f` of the module `M` at the work-item:
every path of its run with memory, when no path chooses more than `budget`
bits in all. -/
def exhaustive (M : Module CoreGpu) (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2)))
    (fuel budget : Nat) : Option (List (Leaf × Nat)) :=
  (modeTree M f args fuel).explore budget

/-- Scripted mode on the function `f` of the module `M` at the work-item:
the path of its run with memory that the choice sequence `cs` names, each
value read by `read`, or why `cs` does not fit the run. -/
def scripted {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (M : Module CoreGpu)
    (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ) :
    Except (ChoiceTree.Misfit σ) (Leaf × Nat) :=
  (modeTree M f args fuel).script read cs 0

/-- Sampled mode on the function `f` of the module `M` at the work-item:
the path of its run with memory on which `draw` gives each choice, from the
generator `g`, and the values chosen on it. -/
def sampled {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (M : Module CoreGpu)
    (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    Leaf × List ChoiceTree.Chosen :=
  (modeTree M f args fuel).sample draw g

/-! # Outcomes of the runs with memory -/

/-- Exhaustive mode, within its choice budget, gives exactly the outcomes
of the run with memory at the fuel budget it runs with. -/
theorem exhaustive_memOutcomes (M : Module CoreGpu) (f : Func CoreGpu)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) {ls : List (Leaf × Nat)}
    (hx : exhaustive M f args fuel budget = some ls) (o : Outcome (List (DVal CoreGpu))) :
    Run.outcomes (f.memRuns M.layout.entry memName M args fuel) o ↔
      ∃ p ∈ ls, p.1.pathEnd = .outcome o := by
  have h := (letI := memTreeDenote M.layout.entry memName
    Func.memExplore_outcomes M.layout.entry memName (memMapsDenote M.layout.entry memName) M f
      args fuel budget hx o)
  exact h

/-- Exhaustive mode, within its choice budget, lists a stuck path exactly
when the run with memory has one. -/
theorem exhaustive_memStuck (M : Module CoreGpu) (f : Func CoreGpu)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) {ls : List (Leaf × Nat)}
    (hx : exhaustive M f args fuel budget = some ls) :
    Run.IsStuck (f.memRuns M.layout.entry memName M args fuel) ↔
      ∃ p ∈ ls, ∃ st, p.1.pathEnd = .stuck st := by
  have h := (letI := memTreeDenote M.layout.entry memName
    Func.memExplore_stuck M.layout.entry memName (memMapsDenote M.layout.entry memName) M f args
      fuel budget hx)
  exact h

/-- Scripted mode, on a choice sequence that fits, gives an outcome of the
run with memory at the fuel budget it runs with. -/
theorem scripted_memOutcomes {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (M : Module CoreGpu) (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (cs : List σ) {l : Leaf} {c : Nat} (hs : scripted read M f args fuel cs = .ok (l, c))
    {o : Outcome (List (DVal CoreGpu))} (ho : l.pathEnd = .outcome o) :
    Run.outcomes (f.memRuns M.layout.entry memName M args fuel) o := by
  have h := (letI := memTreeDenote M.layout.entry memName
    Func.memScript_outcomes M.layout.entry memName (memMapsDenote M.layout.entry memName) read M f
      args fuel cs hs ho)
  exact h

/-- Scripted mode, on a choice sequence that fits, reports a stuck path
only when the run with memory has one. -/
theorem scripted_memStuck {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (M : Module CoreGpu) (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (cs : List σ) {l : Leaf} {c : Nat} (hs : scripted read M f args fuel cs = .ok (l, c))
    {st : Stuck} (hst : l.pathEnd = .stuck st) :
    Run.IsStuck (f.memRuns M.layout.entry memName M args fuel) := by
  have h := (letI := memTreeDenote M.layout.entry memName
    Func.memScript_stuck M.layout.entry memName (memMapsDenote M.layout.entry memName) read M f
      args fuel cs hs hst)
  exact h

/-- The values that sampled mode chose are a choice sequence that fits the
run: scripted mode on them reports the same path, with as many choices. -/
theorem sampled_fits {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (M : Module CoreGpu)
    (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    scripted ChoiceTree.readChosen M f args fuel (sampled draw M f args fuel g).2 =
      .ok ((sampled draw M f args fuel g).1, (sampled draw M f args fuel g).2.length) := by
  have h := ChoiceTree.sample_script (draw := draw) (modeTree M f args fuel) g 0
  rw [Nat.zero_add] at h
  exact h

/-- Sampled mode gives an outcome of the run with memory at the fuel budget
it runs with, whatever the generator. -/
theorem sampled_memOutcomes {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (M : Module CoreGpu) (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (g : γ) {o : Outcome (List (DVal CoreGpu))}
    (ho : (sampled draw M f args fuel g).1.pathEnd = .outcome o) :
    Run.outcomes (f.memRuns M.layout.entry memName M args fuel) o :=
  scripted_memOutcomes _ M f args fuel _ (sampled_fits draw M f args fuel g) ho

/-- Sampled mode reports a stuck path only when the run with memory has
one. -/
theorem sampled_memStuck {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (M : Module CoreGpu) (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (g : γ) {st : Stuck}
    (hst : (sampled draw M f args fuel g).1.pathEnd = .stuck st) :
    Run.IsStuck (f.memRuns M.layout.entry memName M args fuel) :=
  scripted_memStuck _ M f args fuel _ (sampled_fits draw M f args fuel g) hst

end Fir.Gpu
