import Fir.Memory.Refine
import Fir.Memory.Address

/-!
# Exposure laws

Giving an allocation an address changes nothing an access sees. The laws
below say so, and say what the memory's other operations do to addresses:

* Exposing gives the allocation the address only when it has none, and
  changes no other allocation's address.
* It keeps every block's kind, alignment, size, liveness, constness and
  units. So a
  load, aligned or not, gives what it gave and faults for the same reason,
  whether an access is aligned is the same, and a store faults for the same
  reason and gives the memory it gave, exposed.
* A new allocation has no address, and allocating, freeing and storing keep
  every address.
* Refinement compares addresses: exposing the same allocation at the same
  address in memories that refine each other keeps refinement, and in such
  memories the same addresses fit, the canonical layout gives the same, and
  every allocation has the same address.
-/

namespace Fir.Memory

variable {u : Nat}

/-- Giving a block an address keeps it constant or not. -/
@[simp] theorem Block.giveAddr_const (x : Nat) (b : Block u) : (b.giveAddr x).const = b.const := by
  unfold Block.giveAddr; split <;> rfl

/-- Giving a block an address keeps its shape. -/
@[simp] theorem Block.giveAddr_shape (x : Nat) (b : Block u) : (b.giveAddr x).shape = b.shape := by
  unfold Block.giveAddr; split <;> rfl

@[simp] theorem Block.giveAddr_units (x : Nat) (b : Block u) : (b.giveAddr x).units = b.units := by
  unfold Block.giveAddr; split <;> rfl

@[simp] theorem Block.giveAddr_live (x : Nat) (b : Block u) : (b.giveAddr x).live = b.live := by
  unfold Block.giveAddr; split <;> rfl

/-- Writing to a block given an address is giving an address to the block
written. -/
theorem Block.giveAddr_write (x : Nat) (b : Block u) (o : Nat) (us : List (MemUnit u)) :
    (b.giveAddr x).write o us = (b.write o us).giveAddr x := by
  unfold Block.giveAddr Block.write; split <;> simp_all

namespace Memory

/-- The blocks of an exposed memory: the allocation `a`'s given the
address, and every other as it was. -/
theorem expose_getElem? (M : Memory u) (a x j : Nat) :
    (M.expose a x).blocks[j]? = (M.blocks[j]?).map fun b => if a = j then b.giveAddr x else b := by
  simp [expose, List.getElem?_modify]

/-- Exposing keeps whatever of each block giving it an address keeps. -/
theorem expose_map {α : Type} (M : Memory u) (a x : Nat) (f : Block u → α)
    (hf : ∀ b, f (b.giveAddr x) = f b) : (M.expose a x).blocks.map f = M.blocks.map f := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map, expose_getElem?, Option.map_map]
  congr 1
  funext b
  simp only [Function.comp_apply]
  split <;> simp [hf]

/-- Exposing keeps the shape of every block. -/
theorem expose_shapes (M : Memory u) (a x : Nat) :
    (M.expose a x).blocks.map Block.shape = M.blocks.map Block.shape :=
  M.expose_map a x _ (Block.giveAddr_shape x)

/-- Exposing keeps the units of every block. -/
theorem expose_contents (M : Memory u) (a x : Nat) :
    (M.expose a x).blocks.map (·.units) = M.blocks.map (·.units) :=
  M.expose_map a x _ (Block.giveAddr_units x)

/-- An exposed allocation that had no address has the one it was given. -/
theorem addrOf_expose_of_none {M : Memory u} {a : AllocId} (ha : a < M.blocks.length)
    (h : M.addrOf a = none) (x : Nat) : (M.expose a x).addrOf a = some x := by
  unfold addrOf at h ⊢
  rw [expose_getElem?, List.getElem?_eq_getElem ha] at *
  simp_all [Block.giveAddr]

/-- An exposed allocation that had an address keeps it. -/
theorem addrOf_expose_of_some {M : Memory u} {a : AllocId} {y : Nat} (h : M.addrOf a = some y)
    (x : Nat) : (M.expose a x).addrOf a = some y := by
  unfold addrOf at h ⊢
  rw [expose_getElem?]
  cases hb : M.blocks[a]? with
  | none => simp [hb] at h
  | some b =>
    simp only [hb, Option.bind_some] at h
    simp [Block.giveAddr, h]

/-- Exposing changes no other allocation's address. -/
theorem addrOf_expose_ne (M : Memory u) {a a' : AllocId} (h : a ≠ a') (x : Nat) :
    (M.expose a x).addrOf a' = M.addrOf a' := by
  unfold addrOf
  rw [expose_getElem?]
  cases M.blocks[a']? <;> simp [h]

/-- Where an access lands in an exposed memory: where it landed before, in
the block given the address if it is the allocation exposed, or at the
same fault. -/
theorem locate_expose (M : Memory u) (a x : Nat) (p : Pointer) (n : Nat) :
    (M.expose a x).locate p n =
      (M.locate p n).map fun r => (r.1, if a = r.1 then r.2.1.giveAddr x else r.2.1, r.2.2) := by
  unfold locate
  cases p.prov with
  | none => rfl
  | some a' =>
    simp only [expose_getElem?]
    cases M.blocks[a']? with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      by_cases h : a = a' <;> simp [h, Except.map] <;> split <;> simp_all <;> split <;> simp_all

/-- A load from an exposed memory is the load from the memory. -/
theorem load_expose (M : Memory u) (a x : Nat) (p : Pointer) (n : Nat) :
    (M.expose a x).load p n = M.load p n := by
  unfold load
  rw [locate_expose]
  cases M.locate p n with
  | error f => rfl
  | ok r =>
    simp only [Except.map, bind, Except.bind, pure, Except.pure, Block.read]
    split <;> simp

/-- Whether an access is aligned is the same in an exposed memory. -/
theorem aligned_expose (M : Memory u) (a x : Nat) (p : Pointer) (al : Nat) :
    (M.expose a x).aligned p al = M.aligned p al := by
  unfold aligned
  cases p.prov with
  | none => rfl
  | some a' =>
    simp only [expose_getElem?]
    cases M.blocks[a']? with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      split <;> simp [Block.giveAddr] <;> split <;> rfl

/-- An aligned load from an exposed memory is the aligned load from the
memory. -/
theorem loadAligned_expose (M : Memory u) (a x : Nat) (p : Pointer) (n al : Nat) :
    (M.expose a x).loadAligned p n al = M.loadAligned p n al := by
  simp only [loadAligned, load_expose, aligned_expose]

/-- A store to an exposed memory faults as the store to the memory does,
or gives the memory it gives, exposed. -/
theorem store_expose (M : Memory u) (a x : Nat) (p : Pointer) (us : List (MemUnit u)) :
    (M.expose a x).store p us = (M.store p us).map (·.expose a x) := by
  unfold store
  rw [locate_expose]
  cases M.locate p us.length with
  | error f => rfl
  | ok r =>
    obtain ⟨a', b, o⟩ := r
    have hc : (if a = a' then b.giveAddr x else b).const = b.const := by
      split <;> simp [Block.giveAddr_const]
    simp only [Except.map, bind, Except.bind, hc]
    cases b.const
    case true => rfl
    simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
    congr 2
    apply List.ext_getElem?
    intro j
    simp only [expose, List.getElem?_set, List.getElem?_modify, List.length_modify]
    by_cases h₁ : a' = j <;> by_cases h₂ : a = j <;> subst_vars <;>
      simp_all [Block.giveAddr_write]

/-- An aligned store to an exposed memory faults as the aligned store to
the memory does, or gives the memory it gives, exposed. -/
theorem storeAligned_expose (M : Memory u) (a x : Nat) (p : Pointer) (us : List (MemUnit u))
    (al : Nat) : (M.expose a x).storeAligned p us al = (M.storeAligned p us al).map (·.expose a x) := by
  unfold storeAligned
  rw [store_expose, aligned_expose]
  cases M.store p us <;> simp [Except.map] <;> split <;> rfl

/-- A new allocation has no address. -/
theorem addrOf_alloc_new (M : Memory u) (k : AllocKind) (n al : Nat) :
    (M.alloc k n al).2.addrOf M.blocks.length = none := by
  simp [addrOf, alloc]

/-- Allocating keeps every address. -/
theorem addrOf_alloc_lt (M : Memory u) (k : AllocKind) (n al : Nat) {a : AllocId}
    (h : a < M.blocks.length) : (M.alloc k n al).2.addrOf a = M.addrOf a := by
  simp [addrOf, alloc, List.getElem?_append_left h]

/-- Freeing keeps every address. -/
theorem addrOf_free (M : Memory u) (a a' : AllocId) : (M.free a).addrOf a' = M.addrOf a' := by
  unfold addrOf free
  simp only [List.getElem?_modify]
  cases M.blocks[a']? <;> simp <;> split <;> rfl

/-- A store keeps every address. -/
theorem addrOf_store {M M' : Memory u} {p : Pointer} {us : List (MemUnit u)}
    (h : M.store p us = .ok M') (a : AllocId) : M'.addrOf a = M.addrOf a := by
  unfold store at h
  cases hl : M.locate p us.length with
  | error f => simp [hl, bind, Except.bind] at h
  | ok r =>
    obtain ⟨a', b, o⟩ := r
    cases hc : b.const
    case true => simp [hl, hc, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    simp only [hl, hc, bind, Except.bind, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at h
    subst h
    have hb := (locate_eq_ok.mp hl).2.1
    unfold addrOf
    simp only [List.getElem?_set]
    split
    · rename_i h₁
      subst h₁
      split
      · simp [hb, Block.write]
      · simp_all
    · rfl

end Memory

/-! # Refinement -/

/-- Giving the same address to blocks that refine each other keeps
refinement. -/
theorem Block.IsRefinedBy.giveAddr {b b' : Block u} (h : b ⊑ b') (x : Nat) :
    b.giveAddr x ⊑ b'.giveAddr x := by
  obtain ⟨hk, hal, hl, hn, ha, hu⟩ := h
  unfold Block.giveAddr
  rw [ha]
  split
  · exact ⟨hk, hal, hl, hn, ha, hu⟩
  · exact ⟨hk, hal, hl, hn, rfl, hu⟩

/-- Exposing the same allocation at the same address in memories that
refine each other keeps refinement. -/
theorem Memory.IsRefinedBy.expose {M M' : Memory u} (h : M ⊑ M') (a x : Nat) :
    M.expose a x ⊑ M'.expose a x :=
  List.IsRefinedBy.modify (fun hb => Block.IsRefinedBy.giveAddr hb x) h a

/-- Blocks that refine each other leave room for the same addresses. -/
theorem Block.IsRefinedBy.leavesRoom {b b' : Block u} (h : b ⊑ b') (x n : Nat) :
    b.leavesRoom x n = b'.leavesRoom x n := by
  obtain ⟨-, -, hl, hn, ha, -⟩ := h
  simp [Block.leavesRoom, hl, hn, ha]

/-- Lists of blocks that refine each other leave room for the same
addresses. -/
theorem roomFrom_isRefinedBy {x n a : Nat} :
    ∀ {i : Nat} {bs bs' : List (Block u)}, bs ⊑ bs' → roomFrom x n a i bs = roomFrom x n a i bs'
  | _, [], [], _ => rfl
  | i, _ :: bs, _ :: bs', h => by
    simp only [roomFrom, h.1.leavesRoom, roomFrom_isRefinedBy (i := i + 1) (bs := bs) h.2]
  | _, [], _ :: _, h | _, _ :: _, [], h => (h : False).elim

namespace Memory

/-- Memories that refine each other give every allocation the same address. -/
theorem IsRefinedBy.addrOf {M M' : Memory u} (h : M ⊑ M') (a : AllocId) :
    M.addrOf a = M'.addrOf a := by
  unfold Memory.addrOf
  rcases List.IsRefinedBy.getElem? h a with ⟨h₁, h₂⟩ | ⟨b, b', h₁, h₂, hb⟩
  · rw [h₁, h₂]
  · simp [h₁, h₂, hb.2.2.2.2.1]

/-- The same addresses fit in memories that refine each other. -/
theorem IsRefinedBy.fits {M M' : Memory u} (h : M ⊑ M') (lo hi a x : Nat) :
    M.fits lo hi a x = M'.fits lo hi a x := by
  unfold Memory.fits
  rcases List.IsRefinedBy.getElem? h a with ⟨h₁, h₂⟩ | ⟨b, b', h₁, h₂, hb⟩
  · rw [h₁, h₂]
  · simp only [h₁, h₂, hb.2.1, hb.2.2.2.1, roomFrom_isRefinedBy h]

/-- The canonical addresses are the same in lists of blocks that refine
each other. -/
theorem bumpFrom_isRefinedBy :
    ∀ {c : Nat} {bs bs' : List (Block u)}, bs ⊑ bs' → ∀ a, bumpFrom c bs a = bumpFrom c bs' a
  | _, [], [], _, _ => rfl
  | _, _ :: _, _ :: _, h, 0 => by simp only [bumpFrom, h.1.2.1]
  | _, _ :: _, _ :: _, h, a + 1 => by
    simp only [bumpFrom, h.1.2.1, h.1.2.2.2.1]
    exact bumpFrom_isRefinedBy h.2 a
  | _, [], _ :: _, h, _ | _, _ :: _, [], h, _ => (h : False).elim

/-- The address `lowestFrom` gives is the same in memories that refine each
other, over blocks that refine each other. -/
theorem lowestFrom_isRefinedBy {M M' : Memory u} (hM : M ⊑ M') (lo hi a al : Nat) :
    ∀ {best : Option Nat} {cs cs' : List (Block u)}, cs ⊑ cs' →
      lowestFrom M lo hi a al best cs = lowestFrom M' lo hi a al best cs'
  | _, [], [], _ => rfl
  | best, c :: cs, c' :: cs', h => by
    obtain ⟨-, -, hl, hn, ha, -⟩ := h.1
    simp only [lowestFrom, ha, hl, hn, hM.fits]
    exact lowestFrom_isRefinedBy hM lo hi a al h.2
  | _, [], _ :: _, h | _, _ :: _, [], h => (h : False).elim

/-- The lowest address that fits is the same in memories that refine each
other. -/
theorem IsRefinedBy.lowestFit {M M' : Memory u} (h : M ⊑ M') (lo hi a : Nat) :
    M.lowestFit lo hi a = M'.lowestFit lo hi a := by
  unfold Memory.lowestFit
  rcases List.IsRefinedBy.getElem? h a with ⟨h₁, h₂⟩ | ⟨b, b', h₁, h₂, hb⟩
  · rw [h₁, h₂]
  · simp only [h₁, h₂, hb.2.1, IsRefinedBy.fits h]
    exact lowestFrom_isRefinedBy h lo hi a _ h

/-- The canonical layout gives the same address in memories that refine
each other. -/
theorem IsRefinedBy.canonical {M M' : Memory u} (h : M ⊑ M') (lo hi a : Nat) :
    M.canonical lo hi a = M'.canonical lo hi a := by
  unfold Memory.canonical Memory.bump
  rw [bumpFrom_isRefinedBy h a]
  simp only [IsRefinedBy.fits h, IsRefinedBy.lowestFit h]

end Memory

end Fir.Memory
