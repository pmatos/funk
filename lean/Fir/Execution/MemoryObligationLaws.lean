import Fir.Execution.EffectLaws
import Fir.Execution.MemoryRuns

/-!
# Meeting the memory obligations

The memory obligations hold of every computation that keeps the memories,
and they survive a change of the results that keeps the memories:

* a computation with no memory, run in the state layer, keeps the memories
  on every path, so it writes, reads and allocates in no memory;
* mapping the results of a computation changes no memory, so it keeps each
  obligation the computation meets.

So a dialect whose ops touch no memory meets every memory obligation when
it runs each op by its rule in the set monad and keeps the memories
(`DialectMemDenote.ofSetM`), at every naming of its memories, whatever its
ops declare. The core dialect is such a dialect, and so are the dialects of
the tests. A sum and a lift run an op of a side by that side's rule with
its results mapped, so they meet the obligations when their sides do
(the sections on the sum and the lift of dialects lawful in their
effects).
-/

namespace Fir

open Memory

/-! # Renaming memories -/

/-- Renaming the memories of a set twice is renaming them once, by the two
renamings in turn. -/
theorem MemSet.map_map {A B C : Type} (f : A → B) (g : B → C) (s : MemSet A) :
    (s.map f).map g = s.map (g ∘ f) := by
  cases s <;> simp [MemSet.map]

variable {σ α β : Type}

/-- A list is a prefix of itself. The library's proof uses `propext`, and
the effect laws of the test dialects are pinned axiom-free
(`lean/FirTest/Mixed.lean`), so this one uses none. -/
theorem prefix_refl (l : List α) : l <+: l :=
  ⟨[], go l⟩
where
  go : ∀ l : List α, l ++ [] = l
    | [] => rfl
    | a :: l => congrArg (a :: ·) (go l)

/-! # Computations that keep the memories -/

/-- The ways a computation of the set monad, run in the state layer, may
end: as it may, with the state it started from. -/
theorem SetM.lift_apply (x : SetM α) (S : σ) (e : Ev (α × σ)) :
    (StateT.lift x : StateT σ SetM α) S e ↔
      (∃ a, x (.ok a) ∧ e = .ok (a, S)) ∨ (∃ r, x (.ub r) ∧ e = .ub r) :=
  Iff.rfl

/-- The ways a computation with its results mapped may end: as it may, with
each result mapped. -/
theorem SetM.stateMap_apply (f : α → β) (c : StateT σ SetM α) (S : σ) (e : Ev (β × σ)) :
    (f <$> c) S e ↔
      (∃ a S', c S (.ok (a, S')) ∧ e = .ok (f a, S')) ∨ (∃ r, c S (.ub r) ∧ e = .ub r) := by
  show (∃ p, c S (.ok p) ∧ _) ∨ _ ↔ _
  constructor
  · rintro (⟨⟨a, S'⟩, hc, he⟩ | h)
    · exact .inl ⟨a, S', hc, he⟩
    · exact .inr h
  · rintro (⟨a, S', hc, he⟩ | h)
    · exact .inl ⟨(a, S'), hc, he⟩
    · exact .inr h

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] (x : Mem)

omit [DecidableEq Mem] in
/-- A computation with no memory writes no memory. -/
theorem writesNot_lift (c : SetM α) :
    WritesNot (unit := unit) x (StateT.lift c) := by
  intro S a S' h
  rcases (SetM.lift_apply c S _).1 h with ⟨_, -, he⟩ | ⟨_, -, he⟩ <;> cases he
  exact prefix_refl _

/-- A computation with no memory allocates in no memory. -/
theorem allocatesNot_lift (c : SetM α) :
    AllocatesNot (unit := unit) x (StateT.lift c) := by
  intro S a S' h
  rcases (SetM.lift_apply c S _).1 h with ⟨_, -, he⟩ | ⟨_, -, he⟩ <;> cases he
  exact ⟨rfl, rfl⟩

/-- A computation with no memory reads no memory: from any memories it ends
as it ends from any others, with each memory as it was. -/
theorem readsNot_lift (c : SetM α) :
    ReadsNot (unit := unit) x (StateT.lift c) := by
  intro S m hm e h
  rcases (SetM.lift_apply c S _).1 h with ⟨a, ha, rfl⟩ | ⟨r, hr, rfl⟩
  · refine ⟨.ok (a, S.set x m), (SetM.lift_apply c _ _).2 (.inl ⟨a, ha, rfl⟩), rfl,
      ⟨rfl, fun y hy => (S.set_mem_ne m (Ne.symm hy)).symm, ?_⟩, fun _ _ => .inr ⟨rfl, ?_⟩⟩
    · rw [S.set_mem_self]
      exact hm.symm
    · rw [S.set_mem_self]
  · exact ⟨.ub r, (SetM.lift_apply c _ _).2 (.inr ⟨r, hr, rfl⟩), rfl⟩

variable {x} {c : StateT (Memories Mem unit) SetM α} (f : α → β)

omit [DecidableEq Mem] in
/-- Mapping the results keeps a computation that writes no memory `x`. -/
theorem WritesNot.map (h : WritesNot x c) : WritesNot x (f <$> c) := by
  intro S b S' hc
  rcases (SetM.stateMap_apply f c S _).1 hc with ⟨a, S'', hc, he⟩ | ⟨_, -, he⟩ <;> cases he
  exact h S a S' hc

/-- Mapping the results keeps a computation that allocates in no memory
`x`. -/
theorem AllocatesNot.map (h : AllocatesNot x c) : AllocatesNot x (f <$> c) := by
  intro S b S' hc
  rcases (SetM.stateMap_apply f c S _).1 hc with ⟨a, S'', hc, he⟩ | ⟨_, -, he⟩ <;> cases he
  exact h S a S' hc

/-- Mapping the results keeps a computation that reads no memory `x`. -/
theorem ReadsNot.map (h : ReadsNot x c) : ReadsNot x (f <$> c) := by
  intro S m hm e he
  rcases (SetM.stateMap_apply f c S _).1 he with ⟨a, S₁, hc, rfl⟩ | ⟨r, hc, rfl⟩
  · obtain ⟨e', hc', hmatch⟩ := h S m hm _ hc
    rcases e' with ⟨a', S₂⟩ | r'
    · obtain ⟨rfl, hrest⟩ := hmatch
      exact ⟨.ok (f a, S₂), (SetM.stateMap_apply f c _ _).2 (.inl ⟨a, S₂, hc', rfl⟩), rfl, hrest⟩
    · exact (hmatch : False).elim
  · obtain ⟨e', hc', hmatch⟩ := h S m hm _ hc
    rcases e' with ⟨a', S₂⟩ | r'
    · exact (hmatch : False).elim
    · obtain rfl : r = r' := hmatch
      exact ⟨.ub r, (SetM.stateMap_apply f c _ _).2 (.inr ⟨r, hc', rfl⟩), rfl⟩

/-! # Dialects whose ops touch no memory -/

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectEffects d]

/-- The semantics with memory of a dialect whose ops touch no memory: at
every naming, each op runs by its rule in the set monad and keeps the
memories. -/
@[instance_reducible] def DialectMemDenote.ofSetM [DialectDenote d SetM] : DialectMemDenote d :=
  ⟨fun _ _ => DialectDenote.liftState _⟩

variable [DialectDenote d SetM] [DialectCall d] [DialectValidation d]

attribute [local instance] DialectMemDenote.ofSetM in
/-- An op of a dialect whose ops touch no memory writes no memory, at every
naming, whatever it declares: the obligation as `LawfulDialectEffects`
states it. -/
theorem DialectMemDenote.ofSetM_writesNot (op : d.Op) (_ : TypesValid op)
    (_ : isTerminator op = true ∨ callee? op = none) {N : Type} [DecidableEq N] (unit : N → Nat)
    (ρ : DialectEffects.Mem d → N) (x : N) (_ : ¬ ((effects op).writes.map ρ).Has x) :
    OwnRuleHas unit ρ (WritesNot x) op :=
  fun _ => ⟨fun _ => writesNot_lift x _, fun _ => writesNot_lift x _⟩

attribute [local instance] DialectMemDenote.ofSetM in
/-- An op of a dialect whose ops touch no memory reads no memory, at every
naming, whatever it declares. -/
theorem DialectMemDenote.ofSetM_readsNot (op : d.Op) (_ : TypesValid op)
    (_ : isTerminator op = true ∨ callee? op = none) {N : Type} [DecidableEq N] (unit : N → Nat)
    (ρ : DialectEffects.Mem d → N) (x : N) (_ : ¬ ((effects op).reads.map ρ).Has x) :
    OwnRuleHas unit ρ (ReadsNot x) op :=
  fun _ => ⟨fun _ => readsNot_lift x _, fun _ => readsNot_lift x _⟩

attribute [local instance] DialectMemDenote.ofSetM in
/-- An op of a dialect whose ops touch no memory allocates in no memory, at
every naming, whatever it declares. -/
theorem DialectMemDenote.ofSetM_allocatesNot (op : d.Op) (_ : TypesValid op)
    (_ : isTerminator op = true ∨ callee? op = none) {N : Type} [DecidableEq N] (unit : N → Nat)
    (ρ : DialectEffects.Mem d → N) (x : N) (_ : ¬ ((effects op).allocates.map ρ).Has x) :
    OwnRuleHas unit ρ (AllocatesNot x) op :=
  fun _ => ⟨fun _ => allocatesNot_lift x _, fun _ => allocatesNot_lift x _⟩

end Fir
