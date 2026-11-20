import Fir.Memory.Resolver
import Fir.Memory.PolicyLaws

/-!
# Address resolver laws

Whatever a resolver proposes, an integer is turned into a pointer of an
allocation that holds its address, or, when none does, into a pointer with
no provenance. At each call, every allocation that holds the address is the
one picked under some resolver: the one that proposes it at that count.

Memories that refine each other have the same places and hold the same
addresses, so every resolver picks the same allocation in both, and turning
the same integer into a pointer in both gives the same pointer and memories
that refine each other. Turning an integer into a pointer changes no memory
and no frame: it only counts the call.

A pointer exposed and turned back, under the resolver that proposes its
allocation, is the pointer again, while its allocation is live and the
pointer is between its start and its end.
-/

namespace Fir.Memory

variable {u : Nat}

namespace Memory

/-- An allocation that holds an address is one of the memory. -/
theorem lt_of_holds {M : Memory u} {z a : Nat} (h : M.holds z a = true) : a < M.blocks.length := by
  cases hb : M.blocks[a]? with
  | some b => exact (List.getElem?_eq_some_iff.1 hb).1
  | none => simp [holds, hb] at h

/-- What holding an address means: the allocation is live, has an address
`y`, and the address is from `y` to its end. -/
theorem holds_iff {M : Memory u} {z a : Nat} : M.holds z a = true ↔
    ∃ b y, M.blocks[a]? = some b ∧ b.live = true ∧ b.addr = some y ∧ y ≤ z ∧
      z ≤ y + b.units.length := by
  unfold holds
  cases hb : M.blocks[a]? with
  | none => simp
  | some b =>
    cases ha : b.addr with
    | none => simp [ha]
    | some y => simp [ha]

/-- The memory model's pick holds the address. -/
theorem pick_holds {M : Memory u} {z a : Nat} (h : M.pick z = some a) : M.holds z a = true := by
  unfold pick at h
  split at h
  · cases h
    have := List.find?_some ‹_›
    simp only [within, Bool.and_eq_true] at this
    exact this.1
  · exact List.find?_some h

/-- The memory model picks nothing exactly when no allocation holds the
address. -/
theorem pick_eq_none {M : Memory u} {z : Nat} : M.pick z = none ↔ ∀ a, M.holds z a = false := by
  constructor
  · intro h a
    cases ha : M.holds z a with
    | false => rfl
    | true =>
      exfalso
      unfold pick at h
      split at h
      · cases h
      · have := List.find?_eq_none.1 h a (List.mem_range.2 (lt_of_holds ha))
        simp [ha] at this
  · intro h
    have hw : (List.range M.blocks.length).find? (M.within z) = none :=
      List.find?_eq_none.2 fun a _ => by simp [within, h a]
    have hh : (List.range M.blocks.length).find? (M.holds z) = none :=
      List.find?_eq_none.2 fun a _ => by simp [h a]
    simp [pick, hw, hh]

/-- The allocation an address resolves to holds it. -/
theorem resolve_holds {M : Memory u} {z a : Nat} {a? : Option AllocId}
    (h : M.resolve z a? = some a) : M.holds z a = true := by
  cases a? with
  | none => exact pick_holds h
  | some a' =>
    simp only [resolve] at h
    split at h
    · cases h; assumption
    · exact pick_holds h

/-- An address resolves to nothing exactly when no allocation holds it. -/
theorem resolve_eq_none {M : Memory u} {z : Nat} {a? : Option AllocId} :
    M.resolve z a? = none ↔ ∀ a, M.holds z a = false := by
  cases a? with
  | none => exact pick_eq_none
  | some a =>
    simp only [resolve]
    split
    · exact ⟨fun h => (by cases h), fun h => (by simp_all)⟩
    · exact pick_eq_none

/-- An allocation that holds the address is the one it resolves to when the
resolver proposes it. -/
theorem resolve_of_holds {M : Memory u} {z a : Nat} (h : M.holds z a = true) :
    M.resolve z (some a) = some a := by
  simp [resolve, h]

/-- Memories that refine each other hold the same addresses. -/
theorem IsRefinedBy.holds {M M' : Memory u} (h : M ⊑ M') (z a : Nat) :
    M.holds z a = M'.holds z a := by
  unfold Memory.holds
  rcases List.IsRefinedBy.getElem? h a with ⟨h₁, h₂⟩ | ⟨b, b', h₁, h₂, hb⟩
  · rw [h₁, h₂]
  · obtain ⟨-, -, hl, hn, ha, -⟩ := hb
    simp only [h₁, h₂, hl, hn, ha]

/-- Memories that refine each other pick the same allocation for an
address, whatever the resolver proposes. -/
theorem IsRefinedBy.resolve {M M' : Memory u} (h : M ⊑ M') (z : Nat) (a? : Option AllocId) :
    M.resolve z a? = M'.resolve z a? := by
  have hl : M.blocks.length = M'.blocks.length := List.IsRefinedBy.length_eq h
  have hh : M.holds z = M'.holds z := funext (IsRefinedBy.holds h z)
  have hw : M.within z = M'.within z := by
    funext a
    simp only [within, IsRefinedBy.holds h]
  have hp : M.pick z = M'.pick z := by
    simp only [pick, hl, hh, hw]
  cases a? <;> simp only [Memory.resolve, hh, hp]

/-- Memories that refine each other rebuild the same pointer. -/
theorem IsRefinedBy.rebuild {M M' : Memory u} (h : M ⊑ M') (z : Nat) (a? : Option AllocId) :
    M.rebuild z a? = M'.rebuild z a? := by
  cases a? <;> simp only [Memory.rebuild, IsRefinedBy.addrOf h]

end Memory

namespace Memories

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- Turning an integer back into a pointer keeps every memory. -/
@[simp] theorem fromAddr_mem (S : Memories Mem unit) (x : Mem) (k : Resolver) (P : Nat)
    (i : BitVec P) : (S.fromAddr x k P i).2.mem = S.mem := rfl

/-- Turning an integer back into a pointer keeps the frames. -/
@[simp] theorem fromAddr_frames (S : Memories Mem unit) (x : Mem) (k : Resolver) (P : Nat)
    (i : BitVec P) : (S.fromAddr x k P i).2.frames = S.frames := rfl

/-- Turning an integer back into a pointer counts one more call. -/
@[simp] theorem fromAddr_rebuilds (S : Memories Mem unit) (x : Mem) (k : Resolver) (P : Nat)
    (i : BitVec P) : (S.fromAddr x k P i).2.rebuilds = S.rebuilds + 1 := rfl

/-- The pointer that an integer is turned into has the provenance of an
allocation that holds its address, or none, and then no allocation holds
it. -/
theorem fromAddr_prov (S : Memories Mem unit) (x : Mem) (k : Resolver) (P : Nat) (i : BitVec P) :
    (∃ a, (S.fromAddr x k P i).1.prov = some a ∧ (S.mem x).holds i.toNat a = true) ∨
      ((S.fromAddr x k P i).1.prov = none ∧ ∀ a, (S.mem x).holds i.toNat a = false) := by
  unfold Memories.fromAddr
  cases h : (S.mem x).resolve i.toNat (k S.rebuilds (S.mem x).places i.toNat) with
  | some a => exact .inl ⟨a, rfl, Memory.resolve_holds h⟩
  | none => exact .inr ⟨rfl, Memory.resolve_eq_none.1 h⟩

/-- At each call, every allocation that holds the address is the one picked
under some resolver: the one that proposes it. The pointer's offset is the
address less the allocation's. -/
theorem fromAddr_of_holds (S : Memories Mem unit) (x : Mem) (P : Nat) (i : BitVec P) {a : AllocId}
    (h : (S.mem x).holds i.toNat a = true) :
    (S.fromAddr x (fun _ _ _ => some a) P i).1 =
      ⟨some a, (i.toNat : Int) - (((S.mem x).addrOf a).getD 0 : Nat)⟩ := by
  simp only [Memories.fromAddr, Memory.resolve_of_holds h, Memory.rebuild]

/-- Turning an integer back into a pointer in memories that refine each
other gives the same pointer, and memories that refine each other. -/
theorem IsRefinedBy.fromAddr {S S' : Memories Mem unit} (h : S ⊑ S') (x : Mem) (k : Resolver)
    (P : Nat) (i : BitVec P) : (S.fromAddr x k P i).1 = (S'.fromAddr x k P i).1 ∧
      (S.fromAddr x k P i).2 ⊑ (S'.fromAddr x k P i).2 := by
  have hx := h.2.1 x
  refine ⟨?_, h.1, h.2.1, congrArg (· + 1) h.2.2⟩
  simp only [Memories.fromAddr, Memory.IsRefinedBy.places hx, Memory.IsRefinedBy.resolve hx,
    Memory.IsRefinedBy.rebuild hx, h.2.2]

/-- Turning an integer back into a pointer in memories whose memory `x` is
the same and that have counted as many calls gives the same pointer. -/
theorem fromAddr_transfer {S T : Memories Mem unit} {x : Mem} (h : T.mem x = S.mem x)
    (hr : T.rebuilds = S.rebuilds) (k : Resolver) (P : Nat) (i : BitVec P) :
    (T.fromAddr x k P i).1 = (S.fromAddr x k P i).1 := by
  simp only [Memories.fromAddr, h, hr]

/-- A pointer exposed and turned back under the resolver that proposes its
allocation is the pointer again, while the allocation holds the integer
and the sum of its address and the offset is below `2 ^ P`. -/
theorem fromAddr_expose {S S' : Memories Mem unit} {x : Mem} {g : Policy} {P : Nat} {a : AllocId}
    {o : Int} {v : BitVec P} (h : S.expose x g P ⟨some a, o⟩ = some (v, S')) {y : Nat}
    (hy : (S'.mem x).addrOf a = some y) (ho : 0 ≤ o) (hw : y + o.toNat < 2 ^ P)
    (hh : (S'.mem x).holds v.toNat a = true) :
    (S'.fromAddr x (fun _ _ _ => some a) P v).1 = ⟨some a, o⟩ := by
  have hv : v = BitVec.ofInt P (y + o) := by
    have h2 := expose_expose h Policy.canonical
    rw [expose_of_some S' x Policy.canonical P o hy] at h2
    cases h2
    rfl
  have hn : v.toNat = y + o.toNat := by
    subst hv
    have : ((y : Int) + o) = ((y + o.toNat : Nat) : Int) := by omega
    rw [this, BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by exact_mod_cast hw)]
    first | exact Int.toNat_natCast _ | exact Int.toNat_ofNat _ | omega
  rw [fromAddr_of_holds S' x P v hh, hy, hn]
  simp only [Option.getD_some, Pointer.mk.injEq, true_and]
  omega

end Memories

end Fir.Memory
