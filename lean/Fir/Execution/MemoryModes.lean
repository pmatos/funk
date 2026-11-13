import Fir.Execution.Modes
import Fir.Execution.MemoryRuns

/-!
# Exhaustive, scripted and sampled runs with memory

`fir-ref`'s modes walk a tree of choices (the section on exhaustive,
scripted and sampled runs). A run with memory is a run in the state layer
over the set monad, from the empty memories (the section on runs with
memory). So a mode that walks a run with memory walks the run in the state
layer over the tree of choices: its tree is the tree of the run from the
empty memories, and each path of it ends with the memories as they are at
its end. Until observations at the end of a run are designed
([#233](https://github.com/pmatos/funk/issues/233)), an observer sees what
a run returns and not its memories, so the tree that a mode walks drops
the memories at the end of each path.

A dialect's semantics in the state layer over the tree of choices is tied to
its semantics with memory by the morphism through the layer: it maps each
op's computation in the one to its computation in the other, at the naming
of the run's memories. Then the tree of a run with memory has the run with
memory as its set, and the theorems of exhaustive and scripted modes carry
over unchanged: within its budget, exhaustive mode gives exactly the
outcomes of the run with memory, and scripted mode, on a choice sequence
that fits, gives one of them.

A dialect whose ops touch no memory runs in the layer over the tree by
lifting its rules in the tree, as it runs in the layer over the set monad by
lifting its rules there. The morphism through the layer maps the one lift to
the other when it maps the rules in the tree to the rules in the set monad.
-/

namespace Fir

open Memory

/-! # Lifted semantics through the layer -/

section Lift

variable {m n : Type → Type} [Monad m] [Monad n] (φ : MonadMorphism m n)

/-- A morphism through the layer maps a computation with no memory, lifted
into the layer, to its image, lifted. -/
theorem MonadMorphism.state_lift {σ α : Type} (x : m α) :
    (φ.state σ).map (StateT.lift x) = StateT.lift (φ.map x) := by
  funext s
  show φ.map (x >>= fun a => pure (a, s)) = φ.map x >>= fun a => pure (a, s)
  rw [φ.map_bind]
  simp only [φ.map_pure]

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d]

/-- A morphism that maps a dialect's semantics in `m` to its semantics in
`n` maps its lifted semantics in the layer over `m` to its lifted semantics
in the layer over `n`. -/
theorem MonadMorphism.state_mapsDenote_liftState (σ : Type) [DialectDenote d m]
    [DialectDenote d n] (h : φ.MapsDenote (d := d)) :
    letI := DialectDenote.liftState (d := d) (m := m) σ
    letI := DialectDenote.liftState (d := d) (m := n) σ
    (φ.state σ).MapsDenote (d := d) :=
  letI := DialectDenote.liftState (d := d) (m := m) σ
  letI := DialectDenote.liftState (d := d) (m := n) σ
  ⟨fun op args => (φ.state_lift _).trans (congrArg StateT.lift (h.denote op args)),
    fun op args => (φ.state_lift _).trans (congrArg StateT.lift (h.exit op args))⟩

end Lift

/-! # The tree of a run with memory -/

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  {N : Type} [DecidableEq N] (unit : N → Nat) {ε : Type}

/-- The tree of a run with memory of the function `f` of the module `M`, on
`args` with `fuel` steps: its run in the state layer over the tree of
choices, from the empty memories, with the memories dropped at the end of
each path. It is the tree that the modes walk. -/
def Func.memTree [DialectDenote d (StateT (Memories N unit) (ChoiceTree ε))] (M : Module d)
    (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    ChoiceTree ε (Except Stuck (Result (List (DVal d)))) :=
  Prod.fst <$> (f.run M (m := StateT (Memories N unit) (ChoiceTree ε)) args fuel).run.run
    Memories.empty

variable [DialectEffects d] [DialectMemDenote d] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem d → N) [DialectDenote d (StateT (Memories N (unitsOf lay))
      (ChoiceTree ε))]

/-- The dialect's semantics in the layer over the tree of choices denotes its
semantics with memory where a run names its memories by `ρ`: the morphism
through the layer maps each op's computation in the one to its computation
in the other. -/
abbrev MemMapsDenote : Prop :=
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  (ChoiceTree.toSetState ε (Memories N (unitsOf lay))).MapsDenote (d := d)

/-- The tree of a run with memory has the run with memory as its set, when
the semantics in the layer over the tree denotes the semantics with
memory. -/
theorem Func.memTree_toSet (h : MemMapsDenote (d := d) lay (ε := ε) ρ) (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    (f.memTree (unitsOf lay) (ε := ε) M args fuel).toSet = f.memRuns lay ρ M args fuel := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  show ChoiceTree.toSet (Prod.fst <$> _) =
    Prod.fst <$> (f.run M (m := StateT (Memories N (unitsOf lay)) SetM) args fuel).run.run
        Memories.empty
  rw [← Func.run_toSetState h M f args fuel]
  exact ChoiceTree.toSetMorphism.map_map Prod.fst _

/-- Exhaustive mode, within its choice budget, gives exactly the outcomes of
the run with memory at the fuel budget it runs with. -/
theorem Func.memExplore_outcomes (h : MemMapsDenote (d := d) lay (ε := ε) ρ) (M : Module d)
    (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat)
    {ls : List (ChoiceTree.Leaf ε (Except Stuck (Result (List (DVal d)))) × Nat)}
    (hx : (f.memTree (unitsOf lay) M args fuel).explore budget = some ls) (o : Outcome (List (DVal
        d))) :
    Run.outcomes (f.memRuns lay ρ M args fuel) o ↔ ∃ p ∈ ls, p.1.pathEnd = .outcome o := by
  rw [Run.outcomes_iff, ← Func.memTree_toSet lay ρ h, ChoiceTree.explore_toSet hx]
  simp only [ChoiceTree.Leaf.ev?_eq_outcome]

/-- Exhaustive mode, within its choice budget, finds a stuck path exactly
when the run with memory has one. -/
theorem Func.memExplore_stuck (h : MemMapsDenote (d := d) lay (ε := ε) ρ) (M : Module d)
    (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat)
    {ls : List (ChoiceTree.Leaf ε (Except Stuck (Result (List (DVal d)))) × Nat)}
    (hx : (f.memTree (unitsOf lay) M args fuel).explore budget = some ls) :
    Run.IsStuck (f.memRuns lay ρ M args fuel) ↔ ∃ p ∈ ls, ∃ st, p.1.pathEnd = .stuck st := by
  simp only [Run.IsStuck, ← Func.memTree_toSet lay ρ h, ChoiceTree.explore_toSet hx]
  constructor
  · rintro ⟨st, p, hp, he⟩
    exact ⟨p, hp, (ChoiceTree.Leaf.ev?_eq_stuck p.1).1 ⟨st, he⟩⟩
  · rintro ⟨p, hp, hs⟩
    obtain ⟨st, he⟩ := (ChoiceTree.Leaf.ev?_eq_stuck p.1).2 hs
    exact ⟨st, p, hp, he⟩

/-- Scripted mode, on a choice sequence that fits, gives an outcome of the
run with memory at the fuel budget it runs with. -/
theorem Func.memScript_outcomes (h : MemMapsDenote (d := d) lay (ε := ε) ρ) {σ : Type}
    (read : (w : Nat) → σ → Option (BitVec w)) (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ)
    {l : ChoiceTree.Leaf ε (Except Stuck (Result (List (DVal d))))} {c : Nat}
    (hs : (f.memTree (unitsOf lay) M args fuel).script read cs 0 = .ok (l, c))
    {o : Outcome (List (DVal d))} (ho : l.pathEnd = .outcome o) :
    Run.outcomes (f.memRuns lay ρ M args fuel) o := by
  rw [Run.outcomes_iff, ← Func.memTree_toSet lay ρ h]
  exact ChoiceTree.script_toSet hs ((ChoiceTree.Leaf.ev?_eq_outcome l o).2 ho)

/-- Scripted mode, on a choice sequence that fits, finds a stuck path only
when the run with memory has one. -/
theorem Func.memScript_stuck (h : MemMapsDenote (d := d) lay (ε := ε) ρ) {σ : Type}
    (read : (w : Nat) → σ → Option (BitVec w)) (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ)
    {l : ChoiceTree.Leaf ε (Except Stuck (Result (List (DVal d))))} {c : Nat}
    (hs : (f.memTree (unitsOf lay) M args fuel).script read cs 0 = .ok (l, c))
    {st : Stuck} (hst : l.pathEnd = .stuck st) :
    Run.IsStuck (f.memRuns lay ρ M args fuel) := by
  obtain ⟨st', he⟩ := (ChoiceTree.Leaf.ev?_eq_stuck l).2 ⟨st, hst⟩
  exact ⟨st', by rw [← Func.memTree_toSet lay ρ h]; exact ChoiceTree.script_toSet hs he⟩

end Fir
