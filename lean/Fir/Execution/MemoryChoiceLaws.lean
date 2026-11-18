import Fir.Execution.MemoryBindLaws

/-!
# Choices in the state layer

An op whose rule chooses bits and then runs a computation of the state
layer on them, as a copy with a poison length chooses its length, meets an
obligation when the computation does on every choice. A choice of `w` bits
in the state layer keeps the memories and reads none: from any memories it
ends with any `w` bits and those memories, and never in UB. So the ways
such a rule may end are the ways the computation may end on some bits:

* it has an outcome, and finitely many, since `w` bits take `2 ^ w`
  values;
* it writes no unit of a memory, neither allocates nor frees in one, and
  reads none, when the computation does not on any bits;
* it refines another such rule when the computation on each bits refines
  the other's on the same bits, and a rule refines a computation that the
  rule's computation on some bits refines, since the rule may make that
  choice.

Such a rule's other ends, returning a value at once or UB, are the lifts
of returning it and of UB in the set monad, so the laws of a lift apply to
them.
-/

namespace Fir

open Memory

variable {σ α : Type}

/-- `pure` in the state layer over the set monad is the lift of `pure`. -/
theorem SetM.statePure_lift (a : α) : (pure a : StateT σ SetM α) = StateT.lift (pure a) :=
  funext fun S => (SetM.pure_bind a fun b => (pure (b, S) : SetM _)).symm

/-- UB in the state layer over the set monad is the lift of UB. -/
theorem SetM.stateUB_lift (r : String) :
    (MonadUB.ub r : StateT σ SetM α) = StateT.lift (MonadUB.ub r) :=
  funext fun _ => (SetM.ub_bind r _).symm

/-- The ways a choice of `w` bits in the state layer may end: with some
bits, and the state it started from. -/
theorem SetM.stateChoose_apply (w : Nat) (S : σ) (e : Ev (BitVec w × σ)) :
    (MonadChoice.choose w : StateT σ SetM (BitVec w)) S e ↔ ∃ b, e = .ok (b, S) := by
  show (∃ a, (∃ b, Ev.ok a = .ok b) ∧ e = .ok (a, S)) ∨
    (∃ r, (∃ b, Ev.ub (α := BitVec w) r = .ok b) ∧ _) ↔ _
  constructor
  · rintro (⟨a, -, rfl⟩ | ⟨_, ⟨_, h⟩, -⟩)
    · exact ⟨a, rfl⟩
    · cases h
  · rintro ⟨b, rfl⟩
    exact .inl ⟨b, ⟨b, rfl⟩, rfl⟩

variable {w : Nat} {f f' : BitVec w → StateT σ SetM α}

/-- The ways a choice of `w` bits then `f` may end: as `f` may on some
bits, from the same state. -/
theorem SetM.chooseBind_apply (f : BitVec w → StateT σ SetM α) (S : σ) (e : Ev (α × σ)) :
    (MonadChoice.choose w >>= f) S e ↔ ∃ b, f b S e := by
  rw [SetM.stateBind_apply]
  constructor
  · rintro (⟨b, S₁, hc, hf⟩ | ⟨_, hc, -⟩)
    · obtain ⟨_, he⟩ := (SetM.stateChoose_apply w S _).1 hc
      cases he
      exact ⟨b, hf⟩
    · obtain ⟨_, he⟩ := (SetM.stateChoose_apply w S _).1 hc
      cases he
  · rintro ⟨b, hf⟩
    exact .inl ⟨b, S, (SetM.stateChoose_apply w S _).2 ⟨b, rfl⟩, hf⟩

/-- A choice then `f` has an outcome when `f` has one on every bits. -/
theorem HasOutcome.chooseBind (hf : ∀ b, HasOutcome (f b)) :
    HasOutcome (MonadChoice.choose w >>= f) := fun S => by
  obtain ⟨e, he⟩ := hf 0 S
  exact ⟨e, (SetM.chooseBind_apply f S e).2 ⟨0, he⟩⟩

/-- A choice then `f` has finitely many outcomes when `f` has on every
bits: `w` bits take finitely many values. -/
theorem FinitelyMany.chooseBind (hf : ∀ b, FinitelyMany (f b)) :
    FinitelyMany (MonadChoice.choose w >>= f) := fun S => by
  obtain ⟨C, hC⟩ := List.exists_cover (L := ChoiceTree.allBits w) (P := fun b x => f b S (.ok x))
    fun b _ => hf b S
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨b, hb⟩ := (SetM.chooseBind_apply f S _).1 hx
  exact hC b (ChoiceTree.mem_allBits b) x hb

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] {x : Mem}
  {g : BitVec w → StateT (Memories Mem unit) SetM α}

/-- A choice then `g` writes no unit of `x` when `g` does not on any
bits. -/
theorem WritesNot.chooseBind (hg : ∀ b, WritesNot x (g b)) :
    WritesNot x (MonadChoice.choose w >>= g) := fun S a S' h => by
  obtain ⟨b, hb⟩ := (SetM.chooseBind_apply g S _).1 h
  exact hg b S a S' hb

/-- A choice then `g` neither allocates nor frees in `x` when `g` does not
on any bits. -/
theorem AllocatesNot.chooseBind (hg : ∀ b, AllocatesNot x (g b)) :
    AllocatesNot x (MonadChoice.choose w >>= g) := fun S a S' h => by
  obtain ⟨b, hb⟩ := (SetM.chooseBind_apply g S _).1 h
  exact hg b S a S' hb

/-- A choice then `g` does not read `x` when `g` does not on any bits: the
choice reads nothing, so the run from the memories with `x` replaced may
make the same choice. -/
theorem ReadsNot.chooseBind (hg : ∀ b, ReadsNot x (g b)) :
    ReadsNot x (MonadChoice.choose w >>= g) := fun S m hm e he => by
  obtain ⟨b, hb⟩ := (SetM.chooseBind_apply g S e).1 he
  obtain ⟨e', he', hmatch⟩ := hg b S m hm e hb
  exact ⟨e', (SetM.chooseBind_apply g _ e').2 ⟨b, he'⟩, hmatch⟩

variable [HRefinement σ σ] {r : α → α → Prop}

/-- A choice then `f'` refines a choice then `f` when `f'` on each bits
refines `f` on the same bits. -/
theorem StateRefinedBy.chooseBind (hf : ∀ b, StateRefinedBy r (f b) (f' b)) :
    StateRefinedBy r (MonadChoice.choose w >>= f) (MonadChoice.choose w >>= f') :=
  fun S S' hS e he => by
  obtain ⟨b, hb⟩ := (SetM.chooseBind_apply f' S' e).1 he
  obtain ⟨e₀, he₀, hle⟩ := hf b S S' hS e hb
  exact ⟨e₀, (SetM.chooseBind_apply f S e₀).2 ⟨b, he₀⟩, hle⟩

/-- A computation refines a choice then `f` when it refines `f` on some
bits `b`: the choice may give `b`. -/
theorem StateRefinedBy.chooseBind_left (b : BitVec w) {c' : StateT σ SetM α}
    (h : StateRefinedBy r (f b) c') : StateRefinedBy r (MonadChoice.choose w >>= f) c' :=
  fun S S' hS e he => by
  obtain ⟨e₀, he₀, hle⟩ := h S S' hS e he
  exact ⟨e₀, (SetM.chooseBind_apply f S e₀).2 ⟨b, he₀⟩, hle⟩

end Fir
