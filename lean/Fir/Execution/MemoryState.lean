import Fir.Execution.ChoiceTree
import Fir.Execution.MemoryEffect

/-!
# The state layer

A monad with choice and UB, such as the set monad or the tree of choices,
has no memory. The _state layer_ over it adds the memories of a run: a
computation takes the memories as they are before it, and gives each of the
ways it may end with the memories as they are after it. It is Lean's
`StateT`, over the memories of the section on the memories of a run. It
keeps the effects of the monad below it, and adds two:

* choice and UB are those of the monad below. A choice keeps the memories,
  and UB ends the path, so a path that ends in UB shows no memory;
* the memory effect runs the memory model's operations on the memories, and
  an access that faults is the monad's UB, with the fault's reason
  (ADR-2026-11-09-1542);
* a frame enters a call before its computation and leaves it after, so a
  call's stack allocations are freed when it returns
  (ADR-2026-11-09-1548).

The interpreter's computations are `ExceptT Stuck` over the op monad, so in
the state layer a stuck path keeps the memories it reached, and the outcome
of a run ignores them, as it ignores every stuck path.

A monad morphism lifts through the layer: it maps each computation, at each
state, to its image. It keeps choice, UB, frames and the memory effect when
it keeps choice and UB. So the run of a function in the state layer over the
tree of choices maps to its run in the state layer over the set monad, as
the run in the tree maps to the run in the set monad.
-/

namespace Fir

open Memory

variable {σ : Type} {m n : Type → Type}

/-- A choice in the state layer chooses bits, and keeps the state. -/
instance instMonadChoiceStateT [Monad m] [MonadChoice m] : MonadChoice (StateT σ m) :=
  ⟨fun w s => (fun b => (b, s)) <$> MonadChoice.choose w⟩

/-- UB in the state layer is the UB of the monad below: it ends the path. -/
instance instMonadUBStateT [MonadUB m] : MonadUB (StateT σ m) := ⟨fun r _ => MonadUB.ub r⟩

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- A frame in the state layer enters a call before its computation and
leaves the call after. -/
instance instMonadFrameStateT [Monad m] : MonadFrame (StateT (Memories Mem unit) m) :=
  ⟨fun x S => (fun r => (r.1, r.2.exit)) <$> x S.enter⟩

/-- The memory effect in the state layer: the memory model's operations on
the memories of the run. An access that faults is UB, with the reason of
its fault. -/
instance instMonadMemoryStateT [Monad m] [MonadUB m] :
    MonadMemory Mem unit (StateT (Memories Mem unit) m) where
  alloc x k n S := pure (S.alloc x k n)
  free x a S := pure ((), S.free x a)
  load x p n S := match S.load x p n with
    | .ok us => pure (us, S)
    | .error f => MonadUB.ub f.reason
  store x p us S := match S.store x p us with
    | .ok S' => pure ((), S')
    | .error f => MonadUB.ub f.reason

/-!
# Morphisms through the layer
-/

variable [Monad m] [Monad n]

/-- A monad morphism from `m` to `n` is one from the state layer over `m` to
the state layer over `n`: it maps each computation, at each state, to its
image. -/
def MonadMorphism.state (φ : MonadMorphism m n) (σ : Type) :
    MonadMorphism (StateT σ m) (StateT σ n) where
  map x := fun s => φ.map (x s)
  map_pure a := by
    funext s
    exact φ.map_pure (a, s)
  map_bind x f := by
    funext s
    simp only [bind, StateT.bind]
    exact φ.map_bind _ _
  map_map g x := by
    funext s
    simp only [Functor.map, StateT.map]
    rw [φ.map_bind]
    congr 1
    funext p
    exact φ.map_pure _

variable (φ : MonadMorphism m n)

/-- A morphism through the layer maps frames to frames. -/
theorem MonadMorphism.state_mapsFrame : (φ.state (Memories Mem unit)).MapsFrame := by
  intro α x
  funext S
  exact φ.map_map _ (x S.enter)

/-- A morphism that keeps choice keeps it through the layer. -/
theorem MonadMorphism.state_choose [MonadChoice m] [MonadChoice n]
    (h : ∀ w, φ.map (MonadChoice.choose w) = MonadChoice.choose w) (w : Nat) :
    (φ.state σ).map (MonadChoice.choose w) = MonadChoice.choose w := by
  funext s
  show φ.map ((fun b => (b, s)) <$> MonadChoice.choose w) = (fun b => (b, s)) <$> MonadChoice.choose w
  rw [φ.map_map, h]

/-- A morphism that keeps UB keeps it through the layer. -/
theorem MonadMorphism.state_ub [MonadUB m] [MonadUB n]
    (h : ∀ {α : Type} (r : String), φ.map (MonadUB.ub r : m α) = MonadUB.ub r) {α : Type}
    (r : String) : (φ.state σ).map (MonadUB.ub r : StateT σ m α) = MonadUB.ub r := by
  funext s
  exact h r

variable [MonadUB m] [MonadUB n]

/-- A morphism through the layer keeps allocation. -/
theorem MonadMorphism.state_alloc (x : Mem) (k : AllocKind) (size : Nat) :
    (φ.state (Memories Mem unit)).map (MonadMemory.alloc x k size) =
      MonadMemory.alloc (m := StateT (Memories Mem unit) n) x k size := by
  funext S
  exact φ.map_pure _

/-- A morphism through the layer keeps freeing. -/
theorem MonadMorphism.state_free (x : Mem) (a : AllocId) :
    (φ.state (Memories Mem unit)).map (MonadMemory.free x a) =
      MonadMemory.free (m := StateT (Memories Mem unit) n) x a := by
  funext S
  exact φ.map_pure _

section

variable (h : ∀ {α : Type} (r : String), φ.map (MonadUB.ub r : m α) = MonadUB.ub r)
include h

/-- A morphism that keeps UB keeps loads through the layer. -/
theorem MonadMorphism.state_load (x : Mem) (p : Pointer) (k : Nat) :
    (φ.state (Memories Mem unit)).map (MonadMemory.load x p k) =
      MonadMemory.load (m := StateT (Memories Mem unit) n) x p k := by
  funext S
  show φ.map (match S.load x p k with
    | .ok us => pure (us, S)
    | .error f => MonadUB.ub f.reason) = match S.load x p k with
    | .ok us => pure (us, S)
    | .error f => MonadUB.ub f.reason
  split
  · exact φ.map_pure _
  · exact h _

/-- A morphism that keeps UB keeps stores through the layer. -/
theorem MonadMorphism.state_store (x : Mem) (p : Pointer) (us : List (MemUnit (unit x))) :
    (φ.state (Memories Mem unit)).map (MonadMemory.store x p us) =
      MonadMemory.store (m := StateT (Memories Mem unit) n) x p us := by
  funext S
  show φ.map (match S.store x p us with
    | .ok S' => pure ((), S')
    | .error f => MonadUB.ub f.reason) = match S.store x p us with
    | .ok S' => pure ((), S')
    | .error f => MonadUB.ub f.reason
  split
  · exact φ.map_pure _
  · exact h _

end

/-- The tree of choices in the state layer maps to the set monad in the
state layer: `toSet`, at each state. -/
def ChoiceTree.toSetState (ε σ : Type) : MonadMorphism (StateT σ (ChoiceTree ε)) (StateT σ SetM) :=
  (ChoiceTree.toSetMorphism (ε := ε)).state σ

/-- `toSet` through the layer keeps a choice of bits. -/
theorem ChoiceTree.toSetState_choose (ε σ : Type) (w : Nat) :
    (ChoiceTree.toSetState ε σ).map (MonadChoice.choose w) = MonadChoice.choose w :=
  (ChoiceTree.toSetMorphism (ε := ε)).state_choose ChoiceTree.toSet_choose w

/-- `toSet` through the layer keeps UB. -/
theorem ChoiceTree.toSetState_ub (ε σ : Type) {α : Type} (r : String) :
    (ChoiceTree.toSetState ε σ).map (MonadUB.ub r : StateT σ (ChoiceTree ε) α) = MonadUB.ub r :=
  (ChoiceTree.toSetMorphism (ε := ε)).state_ub (ChoiceTree.toSet_ub (ε := ε)) r

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  {ε : Type} [DialectDenote d (StateT (Memories Mem unit) (ChoiceTree ε))]
  [DialectDenote d (StateT (Memories Mem unit) SetM)]

/-- The run of a function in the layer over the tree of choices has, at
each state, its run in the layer over the set monad as its set, when each
op's semantics in the one has its semantics in the other as its set. -/
theorem Func.run_toSetState
    (h : (ChoiceTree.toSetState ε (Memories Mem unit)).MapsDenote (d := d)) (M : Module d)
    (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    ((ChoiceTree.toSetState ε (Memories Mem unit)).except Stuck).map
        (f.run M (m := StateT (Memories Mem unit) (ChoiceTree ε)) args fuel) =
      f.run M (m := StateT (Memories Mem unit) SetM) args fuel :=
  Func.run_map h (ChoiceTree.toSetMorphism.state_mapsFrame) M f args fuel

end Fir
