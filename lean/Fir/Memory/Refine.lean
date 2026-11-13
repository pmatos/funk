import Fir.Memory.FrameLaws
import Fir.Execution.Values

/-!
A pass may replace a poison value by any value of its type
(ADR-2026-10-29-2008). Memory holds values too, unit by unit, so a pass may
also replace a unit of memory that holds poison by any unit, and a run that
starts from such memories refines one that starts from the first. This
section says when the memories of one run refine those of another:

* a unit is refined by itself, and a poison unit by any unit. A unit of bits
  or a fragment of a pointer is refined by nothing else, so that a fragment
  keeps its pointer's provenance;
* a block is refined by a block of the same kind, liveness and size. While
  it is live, the other's units refine its units one by one. No access
  reaches a freed block, so the units of a freed block are not compared,
  and a store to a block that is then freed may be dropped;
* a memory is refined by a memory whose blocks refine its own, one by one,
  in the order they were made. So both have the same allocations, each with
  its kind, size and liveness;
* the memories of a run are refined by memories with the same frames, in
  which each memory refines the memory of the same name.

Refinement of memories is reflexive and transitive. What a run does to its
memories keeps it:

* entering a call and leaving it keep it, so a call made from memories that
  refine others returns, when its callee does, to memories that refine the
  others' too;
* allocating in refined memories gives the same pointer in both, and fresh
  units of poison in both;
* freeing an allocation keeps it;
* a load through the same pointer faults for the same reason in both, or
  loads units of which those from the second refine those from the first;
* a store of units that refine others, through the same pointer, faults for
  the same reason in both, or gives memories that refine each other.
-/

namespace Fir

namespace Memory

variable {u : Nat}

/-! # Units, blocks and memories -/

/-- A unit is refined by itself, and a poison unit by any unit. -/
def MemUnit.IsRefinedBy : MemUnit u → MemUnit u → Prop
  | .poison, _ => True
  | .bits b, v => v = .bits b
  | .frag m p i, v => v = .frag m p i

instance : HRefinement (MemUnit u) (MemUnit u) := ⟨MemUnit.IsRefinedBy⟩

/-- A block is refined by a block of the same kind, liveness and size whose
units, while it is live, refine its units one by one. No access reaches a
freed block, so its units are not compared: a store to it before it is
freed may be dropped. -/
def Block.IsRefinedBy (b b' : Block u) : Prop :=
  b.kind = b'.kind ∧ b.live = b'.live ∧ b.units.length = b'.units.length ∧
    (b.live → b.units ⊑ b'.units)

instance : HRefinement (Block u) (Block u) := ⟨Block.IsRefinedBy⟩

/-- A memory is refined by a memory whose blocks refine its blocks one by
one. -/
def Memory.IsRefinedBy (M M' : Memory u) : Prop := M.blocks ⊑ M'.blocks

instance : HRefinement (Memory u) (Memory u) := ⟨Memory.IsRefinedBy⟩

/-- Refinement of units is reflexive. -/
theorem MemUnit.isRefinedBy_refl : ∀ a : MemUnit u, a ⊑ a
  | .poison => trivial
  | .bits _ | .frag _ _ _ => rfl

/-- Refinement of units is transitive. -/
theorem MemUnit.isRefinedBy_trans : ∀ {a b c : MemUnit u}, a ⊑ b → b ⊑ c → a ⊑ c
  | .poison, _, _, _, _ => trivial
  | .bits _, _, _, rfl, h | .frag _ _ _, _, _, rfl, h => h

/-- Refinement of blocks is reflexive. -/
theorem Block.isRefinedBy_refl (b : Block u) : b ⊑ b :=
  ⟨rfl, rfl, rfl, fun _ => List.isRefinedBy_refl MemUnit.isRefinedBy_refl _⟩

/-- Refinement of blocks is transitive. -/
theorem Block.isRefinedBy_trans {a b c : Block u} (h₁ : a ⊑ b) (h₂ : b ⊑ c) : a ⊑ c :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1, fun hl =>
    List.isRefinedBy_trans MemUnit.isRefinedBy_trans (h₁.2.2.2 hl) (h₂.2.2.2 (h₁.2.1 ▸ hl))⟩

/-- Refinement of memories is reflexive. -/
theorem Memory.isRefinedBy_refl (M : Memory u) : M ⊑ M :=
  List.isRefinedBy_refl Block.isRefinedBy_refl M.blocks

/-- Refinement of memories is transitive. -/
theorem Memory.isRefinedBy_trans {M₁ M₂ M₃ : Memory u} (h₁ : M₁ ⊑ M₂) (h₂ : M₂ ⊑ M₃) : M₁ ⊑ M₃ :=
  List.isRefinedBy_trans Block.isRefinedBy_trans h₁ h₂

/-! # What a memory does keeps refinement -/

/-- Freeing a block keeps refinement. -/
theorem Block.IsRefinedBy.kill {b b' : Block u} (h : b ⊑ b') : b.kill ⊑ b'.kill :=
  ⟨h.1, rfl, h.2.2.1, fun hl => Bool.noConfusion hl⟩

/-- Freeing an allocation keeps refinement. -/
theorem Memory.IsRefinedBy.free {M M' : Memory u} (h : M ⊑ M') (a : AllocId) :
    M.free a ⊑ M'.free a :=
  List.IsRefinedBy.modify Block.IsRefinedBy.kill h a

/-- Allocating in memories that refine each other gives the same pointer,
and memories that refine each other. -/
theorem Memory.IsRefinedBy.alloc {M M' : Memory u} (h : M ⊑ M') (k : AllocKind) (n : Nat) :
    (M.alloc k n).1 = (M'.alloc k n).1 ∧ (M.alloc k n).2 ⊑ (M'.alloc k n).2 := by
  refine ⟨by simp [Memory.alloc, List.IsRefinedBy.length_eq h], ?_⟩
  exact List.IsRefinedBy.append h ⟨Block.isRefinedBy_refl _, trivial⟩

/-- Where an access lands in memories that refine each other: at the same
fault in both, or in the same allocation at the same offset, in live blocks
that refine each other. -/
theorem Memory.IsRefinedBy.locate {M M' : Memory u} (h : M ⊑ M') (p : Pointer) (n : Nat) :
    (∃ f, M.locate p n = .error f ∧ M'.locate p n = .error f) ∨
      ∃ a b b' o, M.locate p n = .ok (a, b, o) ∧ M'.locate p n = .ok (a, b', o) ∧
        b.live ∧ b ⊑ b' := by
  unfold Memory.locate
  cases p.prov with
  | none => exact .inl ⟨_, rfl, rfl⟩
  | some a =>
    rcases List.IsRefinedBy.getElem? h a with ⟨h₁, h₂⟩ | ⟨b, b', h₁, h₂, hb⟩
    · simp only [h₁, h₂]
      exact .inl ⟨_, rfl, rfl⟩
    · simp only [h₁, h₂, hb.2.1, hb.2.2.1]
      split
      · exact .inl ⟨_, rfl, rfl⟩
      split
      · rename_i hl _
        exact .inr ⟨_, _, _, _, rfl, rfl, by rw [hb.2.1]; simpa using hl, hb⟩
      · exact .inl ⟨_, rfl, rfl⟩

/-- A load through the same pointer from memories that refine each other
faults for the same reason in both, or loads units of which the second's
refine the first's. -/
theorem Memory.IsRefinedBy.load {M M' : Memory u} (h : M ⊑ M') (p : Pointer) (n : Nat) :
    (∃ f, M.load p n = .error f ∧ M'.load p n = .error f) ∨
      ∃ us us', M.load p n = .ok us ∧ M'.load p n = .ok us' ∧ us ⊑ us' := by
  unfold Memory.load
  rcases h.locate p n with ⟨f, h₁, h₂⟩ | ⟨a, b, b', o, h₁, h₂, hl, hb⟩
  · rw [h₁, h₂]
    exact .inl ⟨f, rfl, rfl⟩
  · rw [h₁, h₂]
    exact .inr ⟨_, _, rfl, rfl, List.IsRefinedBy.take n (List.IsRefinedBy.drop o (hb.2.2.2 hl))⟩

/-- A store, through the same pointer, of units that refine others, to
memories that refine each other, faults for the same reason in both, or
gives memories that refine each other. -/
theorem Memory.IsRefinedBy.store {M M' : Memory u} (h : M ⊑ M') (p : Pointer)
    {us us' : List (MemUnit u)} (hu : us ⊑ us') :
    (∃ f, M.store p us = .error f ∧ M'.store p us' = .error f) ∨
      ∃ N N', M.store p us = .ok N ∧ M'.store p us' = .ok N' ∧ N ⊑ N' := by
  unfold Memory.store
  rw [← List.IsRefinedBy.length_eq hu]
  rcases h.locate p us.length with ⟨f, h₁, h₂⟩ | ⟨a, b, b', o, h₁, h₂, hl, hb⟩
  · rw [h₁, h₂]
    exact .inl ⟨f, rfl, rfl⟩
  · rw [h₁, h₂]
    have hu' : b.units.take o ++ us ++ b.units.drop (o + us.length) ⊑
        b'.units.take o ++ us' ++ b'.units.drop (o + us'.length) := by
      rw [← List.IsRefinedBy.length_eq hu]
      exact List.IsRefinedBy.append
        (List.IsRefinedBy.append (List.IsRefinedBy.take o (hb.2.2.2 hl)) hu)
        (List.IsRefinedBy.drop _ (hb.2.2.2 hl))
    exact .inr ⟨_, _, rfl, rfl, List.IsRefinedBy.set h a
      ⟨hb.1, hb.2.1, List.IsRefinedBy.length_eq hu', fun _ => hu'⟩⟩

/-! # The memories of a run -/

variable {Mem : Type} {unit : Mem → Nat}

/-- The memories of a run are refined by memories with the same frames, in
which each memory refines the memory of the same name. -/
def Memories.IsRefinedBy (S S' : Memories Mem unit) : Prop :=
  S.frames = S'.frames ∧ ∀ x, S.mem x ⊑ S'.mem x

instance : HRefinement (Memories Mem unit) (Memories Mem unit) := ⟨Memories.IsRefinedBy⟩

namespace Memories

/-- Refinement of the memories of a run is reflexive. -/
theorem isRefinedBy_refl (S : Memories Mem unit) : S ⊑ S :=
  ⟨rfl, fun x => Memory.isRefinedBy_refl (S.mem x)⟩

/-- Refinement of the memories of a run is transitive. -/
theorem isRefinedBy_trans {S₁ S₂ S₃ : Memories Mem unit} (h₁ : S₁ ⊑ S₂) (h₂ : S₂ ⊑ S₃) :
    S₁ ⊑ S₃ :=
  ⟨h₁.1.trans h₂.1, fun x => Memory.isRefinedBy_trans (h₁.2 x) (h₂.2 x)⟩

/-- Entering a call keeps refinement. -/
theorem IsRefinedBy.enter {S S' : Memories Mem unit} (h : S ⊑ S') : S.enter ⊑ S'.enter :=
  ⟨congrArg ([] :: ·) h.1, h.2⟩

variable [DecidableEq Mem]

/-- Replacing a memory by one that refines another's keeps refinement. -/
theorem IsRefinedBy.set {S S' : Memories Mem unit} (h : S ⊑ S') (x : Mem)
    {m m' : Memory (unit x)} (hm : m ⊑ m') : S.set x m ⊑ S'.set x m' := by
  refine ⟨h.1, fun y => ?_⟩
  by_cases hxy : x = y
  · subst hxy
    simpa [Memories.set] using hm
  · simpa [Memories.set, hxy] using h.2 y

/-- Freeing an allocation keeps refinement. -/
theorem IsRefinedBy.free {S S' : Memories Mem unit} (h : S ⊑ S') (x : Mem) (a : AllocId) :
    S.free x a ⊑ S'.free x a :=
  h.set x ((h.2 x).free a)

/-- Freeing each allocation of a list keeps refinement. -/
theorem IsRefinedBy.freeAll : ∀ {S S' : Memories Mem unit}, S ⊑ S' → ∀ l : List (Mem × AllocId),
    S.freeAll l ⊑ S'.freeAll l
  | _, _, h, [] => h
  | _, _, h, (x, a) :: l => IsRefinedBy.freeAll (h.free x a) l

/-- Leaving a call keeps refinement: both free the allocations of the same
frame. -/
theorem IsRefinedBy.exit {S S' : Memories Mem unit} (h : S ⊑ S') : S.exit ⊑ S'.exit := by
  obtain ⟨hf, hm⟩ := h
  unfold Memories.exit
  rw [← hf]
  cases hS : S.frames with
  | nil => exact ⟨hf, hm⟩
  | cons fr frs =>
    exact IsRefinedBy.freeAll (S := { S with frames := frs }) (S' := { S' with frames := frs })
      ⟨rfl, hm⟩ fr

omit [DecidableEq Mem] in
/-- Recording a stack allocation in the innermost frame keeps refinement. -/
theorem IsRefinedBy.record {S S' : Memories Mem unit} (h : S ⊑ S') (x : Mem) (a : AllocId) :
    S.record x a ⊑ S'.record x a := by
  obtain ⟨hf, hm⟩ := h
  unfold Memories.record
  rw [← hf]
  cases hS : S.frames with
  | nil => exact ⟨hf, hm⟩
  | cons fr frs => exact ⟨rfl, hm⟩

/-- Allocating in memories that refine each other gives the same pointer,
and memories that refine each other. -/
theorem IsRefinedBy.alloc {S S' : Memories Mem unit} (h : S ⊑ S') (x : Mem) (k : AllocKind)
    (n : Nat) : (S.alloc x k n).1 = (S'.alloc x k n).1 ∧ (S.alloc x k n).2 ⊑ (S'.alloc x k n).2 := by
  obtain ⟨hp, hm⟩ := (h.2 x).alloc k n
  refine ⟨hp, ?_⟩
  have hs := h.set x hm
  have hl : (S.mem x).blocks.length = (S'.mem x).blocks.length := List.IsRefinedBy.length_eq (h.2 x)
  simp only [Memories.alloc, hl]
  split
  · exact hs.record x _
  · exact hs

omit [DecidableEq Mem] in
/-- A load through the same pointer from memories that refine each other
faults for the same reason in both, or loads units of which the second's
refine the first's. -/
theorem IsRefinedBy.load {S S' : Memories Mem unit} (h : S ⊑ S') (x : Mem) (p : Pointer)
    (n : Nat) : (∃ f, S.load x p n = .error f ∧ S'.load x p n = .error f) ∨
      ∃ us us', S.load x p n = .ok us ∧ S'.load x p n = .ok us' ∧ us ⊑ us' :=
  (h.2 x).load p n

/-- A store, through the same pointer, of units that refine others, to
memories that refine each other, faults for the same reason in both, or
gives memories that refine each other. -/
theorem IsRefinedBy.store {S S' : Memories Mem unit} (h : S ⊑ S') (x : Mem) (p : Pointer)
    {us us' : List (MemUnit (unit x))} (hu : us ⊑ us') :
    (∃ f, S.store x p us = .error f ∧ S'.store x p us' = .error f) ∨
      ∃ T T', S.store x p us = .ok T ∧ S'.store x p us' = .ok T' ∧ T ⊑ T' := by
  unfold Memories.store
  rcases (h.2 x).store p hu with ⟨f, h₁, h₂⟩ | ⟨N, N', h₁, h₂, hN⟩
  · rw [h₁, h₂]
    exact .inl ⟨f, rfl, rfl⟩
  · rw [h₁, h₂]
    exact .inr ⟨_, _, rfl, rfl, h.set x hN⟩

end Memories

end Memory

end Fir
