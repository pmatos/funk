import Fir.Memory.Policy
import Fir.Memory.CanonicalLaws
import Fir.Memory.ExposeLaws

/-!
# Address policy laws

Whatever an address policy proposes, the address given fits, and no address
is given exactly when none fits. Every address that fits is given by some
policy: the one that proposes it. So the runs of every policy together give
an exposed allocation every address that the spec allows, and no other.

Memories that refine each other have the same places, so every policy
proposes the same address in both, and exposing the same pointer in both
gives the same integer and memories that refine each other.

Exposing a pointer changes only its own memory, and there only the address
of its allocation: every block keeps its shape and units, and every other
allocation its address. An allocation exposed once keeps its address, so
exposing it again gives the same integer and the same memories, whatever
the policy.
-/

namespace Fir.Memory

variable {u : Nat}

namespace Memory

/-- The address given always fits. -/
theorem choose_fits {M : Memory u} {lo hi a x : Nat} {y? : Option Nat}
    (h : M.choose lo hi a y? = some x) : M.fits lo hi a x = true := by
  cases y? with
  | none => exact canonical_fits h
  | some y =>
    simp only [choose] at h
    split at h
    · cases h; assumption
    · exact canonical_fits h

/-- No address is given exactly when no address fits. -/
theorem choose_eq_none {M : Memory u} {lo hi a : Nat} {y? : Option Nat} :
    M.choose lo hi a y? = none ↔ ∀ x, M.fits lo hi a x = false := by
  constructor
  · intro h x
    cases hx : M.fits lo hi a x with
    | false => rfl
    | true =>
      obtain ⟨z, hz, -⟩ := exists_fits_iff.1 ⟨x, hx⟩
      cases y? with
      | none => simp [choose, hz] at h
      | some y =>
        simp only [choose] at h
        split at h
        · cases h
        · simp [hz] at h
  · intro h
    have hc : M.canonical lo hi a = none := by
      cases hc : M.canonical lo hi a with
      | none => rfl
      | some z =>
        have hz := canonical_fits hc
        rw [h z] at hz
        cases hz
    cases y? with
    | none => exact hc
    | some y => simp [choose, h y, hc]

/-- An address that fits is the one given when the policy proposes it. -/
theorem choose_of_fits {M : Memory u} {lo hi a y : Nat} (h : M.fits lo hi a y = true) :
    M.choose lo hi a (some y) = some y := by
  simp [choose, h]

/-- An allocation that some address fits is one of the memory. -/
theorem lt_of_fits {M : Memory u} {lo hi a x : Nat} (h : M.fits lo hi a x = true) :
    a < M.blocks.length := by
  obtain ⟨b, hb, -⟩ := fits_eq_true.1 h
  exact (List.getElem?_eq_some_iff.1 hb).1

/-- Memories that refine each other have the same places. -/
theorem IsRefinedBy.places {M M' : Memory u} (h : M ⊑ M') : M.places = M'.places := by
  unfold Memory.places
  obtain ⟨bs⟩ := M
  obtain ⟨bs'⟩ := M'
  change bs ⊑ bs' at h
  induction bs generalizing bs' with
  | nil => cases bs' with
    | nil => rfl
    | cons _ _ => exact (h : False).elim
  | cons b bs ih => cases bs' with
    | nil => exact (h : False).elim
    | cons b' bs' =>
      obtain ⟨hk, hal, hl, hn, ha, -⟩ := h.1
      have := ih bs' h.2
      simp only at this
      simp [Block.shape, hk, hal, hl, hn, ha]
      simpa [Block.shape] using this

/-- Memories that refine each other give the same address on the same
proposal. -/
theorem IsRefinedBy.choose {M M' : Memory u} (h : M ⊑ M') (lo hi a : Nat) (y? : Option Nat) :
    M.choose lo hi a y? = M'.choose lo hi a y? := by
  cases y? <;> simp only [Memory.choose, IsRefinedBy.fits h, IsRefinedBy.canonical h]

end Memory

namespace Memories

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- What exposing a pointer with provenance gives when its allocation has
no address: an address that fits, given by `choose`, and the memories with
the allocation at it. -/
theorem expose_of_none (S : Memories Mem unit) (x : Mem) (g : Policy) (P : Nat) {a : AllocId}
    (o : Int) (h : (S.mem x).addrOf a = none) :
    S.expose x g P ⟨some a, o⟩ = ((S.mem x).choose 1 (addrHi P) a (g (S.mem x).places a)).map
      fun (y : Nat) => (BitVec.ofInt P (y + o), S.set x ((S.mem x).expose a y)) := by
  simp [Memories.expose, h]

/-- Exposing a pointer whose allocation has an address gives that address
plus its offset, and changes nothing. -/
theorem expose_of_some (S : Memories Mem unit) (x : Mem) (g : Policy) (P : Nat) {a : AllocId}
    (o : Int) {y : Nat} (h : (S.mem x).addrOf a = some y) :
    S.expose x g P ⟨some a, o⟩ = some (BitVec.ofInt P (y + o), S) := by
  simp [Memories.expose, h]

/-- Exposing gives no integer exactly when the pointer's allocation has no
address and no address fits it. -/
theorem expose_eq_none (S : Memories Mem unit) (x : Mem) (g : Policy) (P : Nat) (p : Pointer) :
    S.expose x g P p = none ↔ ∃ a, p.prov = some a ∧ (S.mem x).addrOf a = none ∧
      ∀ y, (S.mem x).fits 1 (addrHi P) a y = false := by
  obtain ⟨prov, o⟩ := p
  cases prov with
  | none => simp [Memories.expose]
  | some a =>
    cases h : (S.mem x).addrOf a with
    | some y => simp [expose_of_some S x g P o h, h]
    | none => simp [expose_of_none S x g P o h, Memory.choose_eq_none, h]

/-- Exposing either changes nothing, or gives the pointer's allocation,
which had no address, an address that fits. -/
theorem expose_cases {S S' : Memories Mem unit} {x : Mem} {g : Policy} {P : Nat} {p : Pointer}
    {v : BitVec P} (h : S.expose x g P p = some (v, S')) : S' = S ∨
      ∃ a y, p.prov = some a ∧ (S.mem x).addrOf a = none ∧
        (S.mem x).fits 1 (addrHi P) a y = true ∧ S' = S.set x ((S.mem x).expose a y) := by
  obtain ⟨prov, o⟩ := p
  cases prov with
  | none => simp only [Memories.expose, Option.some.injEq, Prod.mk.injEq] at h; exact .inl h.2.symm
  | some a =>
    cases ha : (S.mem x).addrOf a with
    | some y =>
      rw [expose_of_some S x g P o ha] at h
      cases h
      exact .inl rfl
    | none =>
      rw [expose_of_none S x g P o ha] at h
      cases hc : (S.mem x).choose 1 (addrHi P) a (g (S.mem x).places a) with
      | none => rw [hc] at h; cases h
      | some y =>
        rw [hc] at h
        cases h
        exact .inr ⟨a, y, rfl, ha, Memory.choose_fits hc, rfl⟩

/-- Every address that fits an allocation with no address is given by some
policy: the one that proposes it. -/
theorem expose_of_fits (S : Memories Mem unit) (x : Mem) (P : Nat) {a : AllocId} (o : Int)
    (h : (S.mem x).addrOf a = none) {y : Nat} (hy : (S.mem x).fits 1 (addrHi P) a y = true) :
    S.expose x (fun _ _ => some y) P ⟨some a, o⟩ =
      some (BitVec.ofInt P (y + o), S.set x ((S.mem x).expose a y)) := by
  rw [expose_of_none S x _ P o h, Memory.choose_of_fits hy]
  rfl

/-- Exposing a pointer again, under any policy, gives the same integer and
changes nothing. -/
theorem expose_expose {S S' : Memories Mem unit} {x : Mem} {g : Policy} {P : Nat} {p : Pointer}
    {v : BitVec P} (h : S.expose x g P p = some (v, S')) (g' : Policy) :
    S'.expose x g' P p = some (v, S') := by
  obtain ⟨prov, o⟩ := p
  cases prov with
  | none =>
    simp only [Memories.expose, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Memories.expose]
  | some a =>
    cases ha : (S.mem x).addrOf a with
    | some y =>
      rw [expose_of_some S x g P o ha] at h
      cases h
      exact expose_of_some S x g' P o ha
    | none =>
      rw [expose_of_none S x g P o ha] at h
      cases hc : (S.mem x).choose 1 (addrHi P) a (g (S.mem x).places a) with
      | none => rw [hc] at h; cases h
      | some y =>
        rw [hc] at h
        cases h
        apply expose_of_some _ x g' P o
        rw [set_mem_self]
        exact Memory.addrOf_expose_of_none (Memory.lt_of_fits (Memory.choose_fits hc)) ha y

/-- Exposing in memories that refine each other gives the same integer, or
none in both, and memories that refine each other. -/
theorem IsRefinedBy.expose {S S' : Memories Mem unit} (h : S ⊑ S') (x : Mem) (g : Policy)
    (P : Nat) (p : Pointer) : Option.Rel (fun r r' => r.1 = r'.1 ∧ r.2 ⊑ r'.2)
      (S.expose x g P p) (S'.expose x g P p) := by
  have hx := h.2 x
  obtain ⟨prov, o⟩ := p
  cases prov with
  | none => exact .some ⟨rfl, h⟩
  | some a =>
    cases ha : (S.mem x).addrOf a with
    | some y =>
      rw [expose_of_some S x g P o ha,
        expose_of_some S' x g P o ((Memory.IsRefinedBy.addrOf hx a).symm.trans ha)]
      exact .some ⟨rfl, h⟩
    | none =>
      rw [expose_of_none S x g P o ha,
        expose_of_none S' x g P o ((Memory.IsRefinedBy.addrOf hx a).symm.trans ha),
        Memory.IsRefinedBy.places hx, Memory.IsRefinedBy.choose hx]
      cases (S'.mem x).choose 1 (addrHi P) a (g (S'.mem x).places a) with
      | none => exact .none
      | some y => exact .some ⟨rfl, IsRefinedBy.set h x (Memory.IsRefinedBy.expose hx a y)⟩

end Memories

end Fir.Memory
