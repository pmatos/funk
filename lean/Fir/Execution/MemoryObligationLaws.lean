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

So a dialect whose ops touch no memory meets every memory obligation when it
runs each op by its rule in the set monad and keeps the memories
(`DialectMemDenote.ofSetM`), at every naming of its memories, whatever its
ops declare. The dialects of the tests are such dialects. A sum and a lift
run an op of a side by that side's rule with its results mapped, so they
meet the obligations when their sides do (the sections on the sum and the
lift of dialects lawful in their effects).

No UB fares the same way: mapping keeps it, and a computation of the set
monad with no UB, run in the state layer, has none from any memories. So
such a dialect's semantics with memory lifts its semantics in the set monad,
and its ops meet the obligations on may-UB and poison with memory when they
meet them in the set monad. Each of these holds of one op that is tied, too,
so a dialect can meet the obligations op by op: the core dialect does. The
last section goes back: in a dialect that lifts the set monad, an op that
meets them with memory meets them in the set monad, which is how the
theorems over runs in the set monad use them.
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

omit [DecidableEq Mem] in
/-- Mapping the results keeps a computation that never ends in UB. -/
theorem NoUB.map (h : NoUB c) : NoUB (f <$> c) := by
  intro S r hc
  rcases (SetM.stateMap_apply f c S _).1 hc with ⟨_, _, -, he⟩ | ⟨r', hr, he⟩
  · cases he
  · cases he
    exact h S _ hr

omit [DecidableEq Mem] in
/-- A computation of the set monad that never ends in UB, run in the state
layer, never ends in UB. -/
theorem noUB_lift {c : SetM α} (h : ∀ r, ¬ c (.ub r)) :
    NoUB (unit := unit) (StateT.lift c) := by
  intro S r hc
  rcases (SetM.lift_apply c S _).1 hc with ⟨_, -, he⟩ | ⟨r', hr, he⟩
  · cases he
  · cases he
    exact h _ hr

omit [DecidableEq Mem] in
/-- A computation of the set monad that, run in the state layer, never ends
in UB from some memories never ends in UB. -/
theorem NoUB.of_lift {c : SetM α} (h : NoUB (unit := unit) (StateT.lift c))
    (S : Memories Mem unit) (r : String) : ¬ c (.ub r) :=
  fun hc => h S r ((SetM.lift_apply c S _).2 (.inr ⟨r, hc, rfl⟩))

/-! # Dialects whose ops touch no memory -/

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectEffects d]

/-- The semantics with memory of a dialect whose ops touch no memory: at
every naming, each op runs by its rule in the set monad and keeps the
memories. -/
@[instance_reducible] def DialectMemDenote.ofSetM [DialectDenote d SetM] : DialectMemDenote d :=
  ⟨fun _ _ => DialectDenote.liftState _⟩

variable [DialectDenote d SetM]

/-! # Ops that touch no memory -/

section

variable [DialectMemDenote d] {op : d.Op} (hl : OpLiftsSetM op)
include hl

/-- What an op that touches no memory runs by its own rule has every
property that each computation of the set monad, run in the state layer,
has: no write, no read and no allocation in any memory among them. -/
theorem OwnRuleHas.ofLifts {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem d → N) {P : {α : Type} → StateT (Memories N (unitsOf lay)) SetM α → Prop}
    (hP : ∀ {α : Type} (c : SetM α), P (StateT.lift c)) : OwnRuleHas lay ρ P op :=
  fun args => by
    rw [(hl lay ρ args).1, (hl lay ρ args).2]
    exact ⟨fun _ => hP _, fun _ => hP _⟩

/-- An op that touches no memory and never ends in UB in the set monad never
does with memory, at every naming. -/
theorem NeverUB.ofLifts (h : NeverUBSetM op) : NeverUB op :=
  fun lay ρ args => by
    rw [(hl lay ρ args).1, (hl lay ρ args).2]
    exact ⟨fun ht => noUB_lift fun r => (h args r).1 ht,
      fun ht => noUB_lift fun r => (h args r).2 ht⟩

/-- An op that touches no memory and makes no poison in the set monad makes
none with memory, at every naming. -/
theorem MakesNoPoison.ofLifts [TyPoison d.Ty] (h : MakesNoPoisonSetM op) : MakesNoPoison op := by
  intro ht N _ lay ρ args hnp S rs S' hden
  rw [(hl lay ρ args).1] at hden
  rcases (SetM.lift_apply _ S _).1 hden with ⟨a, ha, he⟩ | ⟨_, -, he⟩
  · cases he
    exact h ht args hnp _ ha
  · cases he

end

section

variable [DialectCall d] [DialectValidation d]

attribute [local instance] DialectMemDenote.ofSetM in
/-- An op of a dialect whose ops touch no memory writes no memory, at every
naming, whatever it declares: the obligation as `LawfulDialectEffects`
states it. -/
theorem DialectMemDenote.ofSetM_writesNot (op : d.Op) (_ : TypesValid op)
    (_ : isTerminator op = true ∨ callee? op = none) {N : Type} [DecidableEq N] (lay : N →
        MemLayout)
    (ρ : DialectEffects.Mem d → N) (x : N) (_ : ¬ ((effects op).writes.map ρ).Has x) :
    OwnRuleHas lay ρ (WritesNot x) op :=
  fun _ => ⟨fun _ => writesNot_lift x _, fun _ => writesNot_lift x _⟩

attribute [local instance] DialectMemDenote.ofSetM in
/-- An op of a dialect whose ops touch no memory reads no memory, at every
naming, whatever it declares. -/
theorem DialectMemDenote.ofSetM_readsNot (op : d.Op) (_ : TypesValid op)
    (_ : isTerminator op = true ∨ callee? op = none) {N : Type} [DecidableEq N] (lay : N →
        MemLayout)
    (ρ : DialectEffects.Mem d → N) (x : N) (_ : ¬ ((effects op).reads.map ρ).Has x) :
    OwnRuleHas lay ρ (ReadsNot x) op :=
  fun _ => ⟨fun _ => readsNot_lift x _, fun _ => readsNot_lift x _⟩

attribute [local instance] DialectMemDenote.ofSetM in
/-- An op of a dialect whose ops touch no memory allocates in no memory, at
every naming, whatever it declares. -/
theorem DialectMemDenote.ofSetM_allocatesNot (op : d.Op) (_ : TypesValid op)
    (_ : isTerminator op = true ∨ callee? op = none) {N : Type} [DecidableEq N] (lay : N →
        MemLayout)
    (ρ : DialectEffects.Mem d → N) (x : N) (_ : ¬ ((effects op).allocates.map ρ).Has x) :
    OwnRuleHas lay ρ (AllocatesNot x) op :=
  fun _ => ⟨fun _ => allocatesNot_lift x _, fun _ => allocatesNot_lift x _⟩

end

attribute [local instance] DialectMemDenote.ofSetM in
/-- The semantics with memory of a dialect whose ops touch no memory lifts
its semantics in the set monad: the two are tied. -/
theorem DialectMemDenote.ofSetM_liftsSetM : LiftsSetM d :=
  ⟨fun _ _ => rfl⟩

attribute [local instance] DialectMemDenote.ofSetM in
/-- An op of a dialect whose ops touch no memory that never ends in UB in the
set monad never does with memory, at every naming. -/
theorem NeverUB.ofSetM {op : d.Op} (h : NeverUBSetM op) : NeverUB op :=
  NeverUB.ofLifts (fun _ _ _ => ⟨rfl, rfl⟩) h

attribute [local instance] DialectMemDenote.ofSetM in
/-- An op of a dialect whose ops touch no memory that makes no poison in the
set monad makes none with memory, at every naming. -/
theorem MakesNoPoison.ofSetM [TyPoison d.Ty] {op : d.Op} (h : MakesNoPoisonSetM op) :
    MakesNoPoison op :=
  MakesNoPoison.ofLifts (fun _ _ _ => ⟨rfl, rfl⟩) h

/-! # Back to the set monad -/

variable [DialectMemDenote d] [LiftsSetM d]

/-- In a dialect that lifts the set monad, an op that never ends in UB with
memory never does in the set monad. -/
theorem NeverUB.setM {op : d.Op} (h : NeverUB op) : NeverUBSetM op := by
  intro args r
  have hu := h (N := Unit) (fun _ => MemLayout.default) (fun _ => ()) args
  rw [LiftsSetM.lifts] at hu
  exact ⟨fun ht => NoUB.of_lift (hu.1 ht) Memories.empty r,
    fun ht => NoUB.of_lift (hu.2 ht) Memories.empty r⟩

/-- In a dialect that lifts the set monad, an op that makes no poison with
memory makes none in the set monad. -/
theorem MakesNoPoison.setM [TyPoison d.Ty] {op : d.Op} (h : MakesNoPoison op) :
    MakesNoPoisonSetM op := by
  intro ht args hnp rs hden
  have hp := h ht (N := Unit) (fun _ => MemLayout.default) (fun _ => ()) args hnp Memories.empty rs
    Memories.empty
  rw [LiftsSetM.lifts] at hp
  exact hp ((SetM.lift_apply _ _ _).2 (.inl ⟨rs, hden, rfl⟩))

end Fir
