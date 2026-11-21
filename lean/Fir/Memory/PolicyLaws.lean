import Fir.Memory.Policy
import Fir.Memory.CanonicalLaws
import Fir.Memory.ExposeLaws

/-!
# Address policy laws

Whatever an address policy proposes, the address given may be given, and
no address is given exactly when none may be. At each exposure, every
address that may be given is the one given under some policy: the one that
proposes it.

Memories that refine each other have the same places, so every policy
proposes the same address in both, and exposing the same pointer in both
gives the same integer and memories that refine each other. Exposing in
memories that agree on the memory exposed in gives the same integer, and
changes them alike.

Exposing a pointer changes only its own memory, and there only the address
of its allocation: every block keeps its shape and units, and every other
allocation its address. An allocation exposed once keeps its address, so
exposing it again gives the same integer and the same memories, whatever
the policy.
-/

namespace Fir.Memory

variable {u : Nat}

/-- A multiple of `al` that is at least `c` is at least `c` aligned up to
`al`. -/
theorem alignUp_le {c al x : Nat} (hx : al ∣ x) (hc : c ≤ x) : alignUp c al ≤ x := by
  unfold alignUp
  split
  · exact hc
  · obtain ⟨m, rfl⟩ := hx
    have hal : 0 < al := Nat.pos_of_ne_zero ‹_›
    have hq : (c + al - 1) / al < m + 1 := by
      rw [Nat.div_lt_iff_lt_mul hal, Nat.succ_mul, Nat.mul_comm m al]
      omega
    rw [Nat.mul_comm al m]
    exact Nat.mul_le_mul_right al (Nat.lt_succ_iff.1 hq)

namespace Memory

/-- An address that fits may be given. -/
theorem admits_of_fits {M : Memory u} {lo hi a x : Nat} (h : M.fits lo hi a x = true) :
    M.admits lo hi a x = true := by
  simp [admits, h]

/-- An allocation that some address may be given is one of the memory. -/
theorem lt_of_admits {M : Memory u} {lo hi a x : Nat} (h : M.admits lo hi a x = true) :
    a < M.blocks.length := by
  cases hb : M.blocks[a]? with
  | some b => exact (List.getElem?_eq_some_iff.1 hb).1
  | none =>
    have hf : M.fits lo hi a x = false := by simp [fits, hb]
    simp [admits, hf, hb] at h

/-- The fallback may be given. -/
theorem fallback_admits {M : Memory u} {lo hi a x : Nat} (h : M.fallback lo hi a = some x) :
    M.admits lo hi a x = true := by
  unfold fallback at h
  split at h
  · cases h
    exact admits_of_fits (canonical_fits ‹_›)
  · split at h
    · split at h
      · cases h; assumption
      · cases h
    · cases h

/-- A freed allocation that some address may be given, though none fits,
may be given the first multiple of its alignment from `lo`. -/
theorem admits_alignUp {M : Memory u} {lo hi a x : Nat} {b : Block u} (hb : M.blocks[a]? = some b)
    (hf : ∀ y, M.fits lo hi a y = false) (h : M.admits lo hi a x = true) :
    M.admits lo hi a (alignUp lo b.align) = true := by
  simp only [admits, hf x, hb, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hl, hlo⟩, hd⟩, hhi⟩ := h
  have hle := alignUp_le hd hlo
  have hd' : b.align ∣ alignUp lo b.align := by
    by_cases h0 : b.align = 0
    · rw [h0] at hd ⊢
      have hx := Nat.eq_zero_of_zero_dvd hd
      simp only [alignUp, ↓reduceIte]
      exact ⟨0, by omega⟩
    · exact dvd_alignUp lo (Nat.pos_of_ne_zero h0)
  simp only [admits, hf, hb, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hl, le_alignUp lo b.align⟩, hd'⟩, by omega⟩

/-- The fallback is none exactly when no address may be given. -/
theorem fallback_eq_none {M : Memory u} {lo hi a : Nat} :
    M.fallback lo hi a = none ↔ ∀ x, M.admits lo hi a x = false := by
  constructor
  · intro h x
    cases hx : M.admits lo hi a x with
    | false => rfl
    | true =>
      exfalso
      unfold fallback at h
      cases hc : M.canonical lo hi a with
      | some z => rw [hc] at h; cases h
      | none =>
        have hf : ∀ y, M.fits lo hi a y = false := fun y => by
          cases hy : M.fits lo hi a y with
          | false => rfl
          | true =>
            obtain ⟨z, hz, -⟩ := exists_fits_iff.1 ⟨y, hy⟩
            rw [hc] at hz; cases hz
        cases hb : M.blocks[a]? with
        | none => have := lt_of_admits hx; simp_all
        | some b =>
          simp only [hc, hb, admits_alignUp hb hf hx, ↓reduceIte] at h
          cases h
  · intro h
    have hc : M.canonical lo hi a = none := by
      cases hc : M.canonical lo hi a with
      | none => rfl
      | some z =>
        have hz := admits_of_fits (canonical_fits hc)
        rw [h z] at hz
        cases hz
    unfold fallback
    rw [hc]
    dsimp only
    split
    · simp [h]
    · rfl

/-- The address given may always be given. -/
theorem choose_admits {M : Memory u} {lo hi a x : Nat} {y? : Option Nat}
    (h : M.choose lo hi a y? = some x) : M.admits lo hi a x = true := by
  cases y? with
  | none => exact fallback_admits h
  | some y =>
    simp only [choose] at h
    split at h
    · cases h; assumption
    · exact fallback_admits h

/-- No address is given exactly when no address may be given. -/
theorem choose_eq_none {M : Memory u} {lo hi a : Nat} {y? : Option Nat} :
    M.choose lo hi a y? = none ↔ ∀ x, M.admits lo hi a x = false := by
  cases y? with
  | none => exact fallback_eq_none
  | some y =>
    simp only [choose]
    split
    · exact ⟨fun h => (by cases h), fun h => (by simp_all)⟩
    · exact fallback_eq_none

/-- An address that may be given is the one given when the policy proposes
it. -/
theorem choose_of_admits {M : Memory u} {lo hi a y : Nat} (h : M.admits lo hi a y = true) :
    M.choose lo hi a (some y) = some y := by
  simp [choose, h]

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

/-- The same addresses may be given in memories that refine each other. -/
theorem IsRefinedBy.admits {M M' : Memory u} (h : M ⊑ M') (lo hi a x : Nat) :
    M.admits lo hi a x = M'.admits lo hi a x := by
  unfold Memory.admits
  rw [IsRefinedBy.fits h]
  rcases List.IsRefinedBy.getElem? h a with ⟨h₁, h₂⟩ | ⟨b, b', h₁, h₂, hb⟩
  · rw [h₁, h₂]
  · obtain ⟨-, hal, hl, hn, -, -⟩ := hb
    simp only [h₁, h₂, hal, hl, hn]

/-- Memories that refine each other give the same address on the same
proposal. -/
theorem IsRefinedBy.choose {M M' : Memory u} (h : M ⊑ M') (lo hi a : Nat) (y? : Option Nat) :
    M.choose lo hi a y? = M'.choose lo hi a y? := by
  have hf : M.fallback lo hi a = M'.fallback lo hi a := by
    unfold Memory.fallback
    rw [IsRefinedBy.canonical h]
    rcases List.IsRefinedBy.getElem? h a with ⟨h₁, h₂⟩ | ⟨b, b', h₁, h₂, hb⟩
    · rw [h₁, h₂]
    · simp only [h₁, h₂, hb.2.1, IsRefinedBy.admits h]
  cases y? <;> simp only [Memory.choose, IsRefinedBy.admits h, hf]

end Memory

namespace Memories

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- Exposing a pointer whose allocation has an address gives that address
plus its offset, and changes nothing. -/
theorem expose_of_some (S : Memories Mem unit) (x : Mem) (g : Policy) (P : Nat) {a : AllocId}
    (o : Int) {y : Nat} (h : (S.mem x).addrOf a = some y) :
    S.expose x g P ⟨some a, o⟩ = some (BitVec.ofInt P (y + o), S) := by
  unfold Memory.addrOf at h
  cases hb : (S.mem x).blocks[a]? with
  | none => simp [hb] at h
  | some b =>
    simp only [hb, Option.bind_some] at h
    simp [Memories.expose, hb, h]

/-- What exposing a pointer gives when its allocation has no address: an
address that may be given, by `choose`, and the memories with the
allocation at it. -/
theorem expose_of_none (S : Memories Mem unit) (x : Mem) (g : Policy) (P : Nat) {a : AllocId}
    (o : Int) {b : Block (unit x)} (hb : (S.mem x).blocks[a]? = some b) (h : b.addr = none) :
    S.expose x g P ⟨some a, o⟩ = ((S.mem x).choose 1 (addrHi P) a (g (S.mem x).places a)).map
      fun (y : Nat) => (BitVec.ofInt P (y + o), S.set x ((S.mem x).expose a y)) := by
  simp [Memories.expose, hb, h]

/-- Exposing in memories whose memory `x` is the same gives the same
integer, or none in both, and keeps both memories, or replaces `x` in both
by the same memory. -/
theorem expose_transfer {S T : Memories Mem unit} {x : Mem} (h : T.mem x = S.mem x) (g : Policy)
    (P : Nat) (p : Pointer) : Option.Rel (fun r r' => r.1 = r'.1 ∧
      (r.2 = S ∧ r'.2 = T ∨ ∃ M, r.2 = S.set x M ∧ r'.2 = T.set x M))
      (S.expose x g P p) (T.expose x g P p) := by
  obtain ⟨prov, o⟩ := p
  unfold Memories.expose
  rw [h]
  cases prov with
  | none => exact .some ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  | some a =>
    dsimp only
    cases (S.mem x).blocks[a]? with
    | none => exact .some ⟨rfl, .inl ⟨rfl, rfl⟩⟩
    | some b =>
      dsimp only
      cases b.addr with
      | some y => exact .some ⟨rfl, .inl ⟨rfl, rfl⟩⟩
      | none =>
        dsimp only
        cases (S.mem x).choose 1 (addrHi P) a (g (S.mem x).places a) with
        | none => exact .none
        | some y => exact .some ⟨rfl, .inr ⟨_, rfl, rfl⟩⟩

/-- Exposing gives no integer exactly when the pointer's allocation is one
of the memory, has no address, and no address from `1` to `2 ^ P - 1` may
be given to it. -/
theorem expose_eq_none (S : Memories Mem unit) (x : Mem) (g : Policy) (P : Nat) (p : Pointer) :
    S.expose x g P p = none ↔ ∃ a b, p.prov = some a ∧ (S.mem x).blocks[a]? = some b ∧
      b.addr = none ∧ ∀ y, (S.mem x).admits 1 (addrHi P) a y = false := by
  obtain ⟨prov, o⟩ := p
  cases prov with
  | none => simp [Memories.expose]
  | some a =>
    cases hb : (S.mem x).blocks[a]? with
    | none => simp [Memories.expose, hb]
    | some b =>
      cases ha : b.addr with
      | some y => simp [Memories.expose, hb, ha]
      | none =>
        rw [expose_of_none S x g P o hb ha]
        simp [Memory.choose_eq_none, hb, ha]

/-- Exposing either changes nothing, or gives the pointer's allocation,
which had no address, one that may be given. -/
theorem expose_cases {S S' : Memories Mem unit} {x : Mem} {g : Policy} {P : Nat} {p : Pointer}
    {v : BitVec P} (h : S.expose x g P p = some (v, S')) : S' = S ∨
      ∃ a y, p.prov = some a ∧ (S.mem x).addrOf a = none ∧
        (S.mem x).admits 1 (addrHi P) a y = true ∧ S' = S.set x ((S.mem x).expose a y) := by
  obtain ⟨prov, o⟩ := p
  cases prov with
  | none => simp only [Memories.expose, Option.some.injEq, Prod.mk.injEq] at h; exact .inl h.2.symm
  | some a =>
    cases hb : (S.mem x).blocks[a]? with
    | none =>
      simp only [Memories.expose, hb, Option.some.injEq, Prod.mk.injEq] at h
      exact .inl h.2.symm
    | some b =>
      cases ha : b.addr with
      | some y =>
        simp only [Memories.expose, hb, ha, Option.some.injEq, Prod.mk.injEq] at h
        exact .inl h.2.symm
      | none =>
        rw [expose_of_none S x g P o hb ha] at h
        cases hc : (S.mem x).choose 1 (addrHi P) a (g (S.mem x).places a) with
        | none => rw [hc] at h; cases h
        | some y =>
          rw [hc] at h
          cases h
          exact .inr ⟨a, y, rfl, by simp [Memory.addrOf, hb, ha], Memory.choose_admits hc, rfl⟩

/-- At each exposure, every address that may be given to an allocation
with no address is the one given under some policy: the one that proposes
it. -/
theorem expose_of_admits (S : Memories Mem unit) (x : Mem) (P : Nat) {a : AllocId} (o : Int)
    {b : Block (unit x)} (hb : (S.mem x).blocks[a]? = some b) (h : b.addr = none) {y : Nat}
    (hy : (S.mem x).admits 1 (addrHi P) a y = true) :
    S.expose x (fun _ _ => some y) P ⟨some a, o⟩ =
      some (BitVec.ofInt P (y + o), S.set x ((S.mem x).expose a y)) := by
  rw [expose_of_none S x _ P o hb h, Memory.choose_of_admits hy]
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
    cases hb : (S.mem x).blocks[a]? with
    | none =>
      simp only [Memories.expose, hb, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [Memories.expose, hb]
    | some b =>
      cases ha : b.addr with
      | some y =>
        simp only [Memories.expose, hb, ha, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [Memories.expose, hb, ha]
      | none =>
        rw [expose_of_none S x g P o hb ha] at h
        cases hc : (S.mem x).choose 1 (addrHi P) a (g (S.mem x).places a) with
        | none => rw [hc] at h; cases h
        | some y =>
          rw [hc] at h
          cases h
          apply expose_of_some _ x g' P o
          rw [set_mem_self]
          exact Memory.addrOf_expose_of_none (Memory.lt_of_admits (Memory.choose_admits hc))
            (by simp [Memory.addrOf, hb, ha]) y

/-- Exposing in memories that refine each other gives the same integer, or
none in both, and memories that refine each other. -/
theorem IsRefinedBy.expose {S S' : Memories Mem unit} (h : S ⊑ S') (x : Mem) (g : Policy)
    (P : Nat) (p : Pointer) : Option.Rel (fun r r' => r.1 = r'.1 ∧ r.2 ⊑ r'.2)
      (S.expose x g P p) (S'.expose x g P p) := by
  have hx := h.2.1 x
  obtain ⟨prov, o⟩ := p
  cases prov with
  | none => exact .some ⟨rfl, h⟩
  | some a =>
    rcases List.IsRefinedBy.getElem? hx a with ⟨h₁, h₂⟩ | ⟨b, b', h₁, h₂, hb⟩
    · simp only [Memories.expose] at h₁ h₂ ⊢
      rw [h₁, h₂]
      exact .some ⟨rfl, h⟩
    · have ha : b'.addr = b.addr := hb.2.2.2.2.1.symm
      cases hab : b.addr with
      | some y =>
        simp only [Memories.expose, h₁, h₂, hab, ha]
        exact .some ⟨rfl, h⟩
      | none =>
        rw [expose_of_none S x g P o h₁ hab, expose_of_none S' x g P o h₂ (ha.trans hab),
          Memory.IsRefinedBy.places hx, Memory.IsRefinedBy.choose hx]
        cases (S'.mem x).choose 1 (addrHi P) a (g (S'.mem x).places a) with
        | none => exact .none
        | some y => exact .some ⟨rfl, IsRefinedBy.set h x (Memory.IsRefinedBy.expose hx a y)⟩

end Memories

end Fir.Memory
