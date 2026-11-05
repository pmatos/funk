import FirRef.Dominance.Tree

/-!
A tree over the reached blocks, given by the parent `par` of each block and
rooted at the entry `e`, and what `fir-ref` computes in it. Each block has a
number, `pre`, above its parent's (`Shaped`), so following parents from any
block ends at the entry. `Ancestor par e x y` holds when `x` is `y` or one of its
ancestors. `nca` finds the nearest common ancestor of two blocks by walking
up from the one with the larger number. `Above` is a path of the graph that,
after its first block, enters only blocks numbered above a bound.
-/

namespace FirRef.Dom

open Fir

/-- `x` is `y` or an ancestor of `y`: following `par` up from `y`, never
past the root `e`, reaches `x`. -/
inductive Ancestor (par : Name → Name) (e : Name) (x : Name) : Name → Prop
  | refl : Ancestor par e x x
  | up {y : Name} : y ≠ e → Ancestor par e x (par y) → Ancestor par e x y

/-- `par` is a tree over the blocks `R`, rooted at `e`, in which each block
is numbered above its parent. -/
structure Shaped (par : Name → Name) (pre : Name → Nat) (R : Name → Prop) (e : Name) : Prop where
  root : R e
  root_pre : pre e = 0
  up : ∀ y, R y → y ≠ e → R (par y) ∧ pre (par y) < pre y

variable {par : Name → Name} {pre : Name → Nat} {R : Name → Prop} {e : Name}

namespace Ancestor

theorem trans {x y z : Name} (h₁ : Ancestor par e x y) (h₂ : Ancestor par e y z) :
    Ancestor par e x z := by
  induction h₂ with
  | refl => exact h₁
  | up hz _ ih => exact .up hz ih

theorem root {x : Name} (h : Ancestor par e x e) : x = e := by
  cases h with
  | refl => rfl
  | up he _ => exact absurd rfl he

theorem inv {x y : Name} (h : Ancestor par e x y) (hne : x ≠ y) :
    y ≠ e ∧ Ancestor par e x (par y) := by
  cases h with
  | refl => exact absurd rfl hne
  | up hy h => exact ⟨hy, h⟩

/-- The ancestors of a block form a chain. -/
theorem linear {x y z : Name} (hx : Ancestor par e x z) (hy : Ancestor par e y z) :
    Ancestor par e x y ∨ Ancestor par e y x := by
  induction hx generalizing y with
  | refl => exact .inr hy
  | up hz hx ih =>
    cases hy with
    | refl => exact .inl (.up hz hx)
    | up _ hy => exact ih hy

theorem mem (h : Shaped par pre R e) {x y : Name} (hxy : Ancestor par e x y) (hy : R y) : R x := by
  induction hxy with
  | refl => exact hy
  | up hne _ ih => exact ih (h.up _ hy hne).1

theorem pre_le (h : Shaped par pre R e) {x y : Name} (hxy : Ancestor par e x y) (hy : R y) :
    pre x ≤ pre y := by
  induction hxy with
  | refl => exact Nat.le_refl _
  | up hne _ ih =>
    have := h.up _ hy hne
    exact Nat.le_trans (ih this.1) (Nat.le_of_lt this.2)

theorem pre_lt (h : Shaped par pre R e) {x y : Name} (hxy : Ancestor par e x y) (hy : R y)
    (hne : x ≠ y) : pre x < pre y := by
  obtain ⟨hye, hp⟩ := hxy.inv hne
  have := h.up _ hy hye
  exact Nat.lt_of_le_of_lt (hp.pre_le h this.1) this.2

/-- An ancestor with the same number is the block itself. -/
theorem eq_of_pre (h : Shaped par pre R e) {x y : Name} (hxy : Ancestor par e x y) (hy : R y)
    (hp : pre y ≤ pre x) : x = y :=
  Classical.byContradiction fun hne => absurd hp (Nat.not_le.mpr (hxy.pre_lt h hy hne))

end Ancestor

theorem Shaped.pre_pos (h : Shaped par pre R e) {y : Name} (hy : R y) (hye : y ≠ e) :
    0 < pre y :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (h.up y hy hye).2

/-! # Nearest common ancestors -/

/-- The nearest common ancestor of `x` and `y`: while they differ, the one
with the larger number moves to its parent. The checks on the numbers make
the walk end on any input; on a shaped tree they always pass. -/
def nca (par : Name → Name) (pre : Name → Nat) (x y : Name) : Name :=
  if x = y then x
  else if pre y < pre x then
    if pre (par x) < pre x then nca par pre (par x) y else x
  else if pre (par y) < pre y then nca par pre x (par y) else y
termination_by pre x + pre y

/-- What `nca` finds: a common ancestor of both blocks, below every other
common ancestor. -/
theorem nca_spec (h : Shaped par pre R e) {x y : Name} (hx : R x) (hy : R y) :
    R (nca par pre x y) ∧ Ancestor par e (nca par pre x y) x ∧ Ancestor par e (nca par pre x y) y ∧
      ∀ z, Ancestor par e z x → Ancestor par e z y → Ancestor par e z (nca par pre x y) := by
  fun_induction nca par pre x y with
  | case1 x => exact ⟨hx, .refl, .refl, fun _ h _ => h⟩
  | case2 x y hne hlt _ ih =>
    have hxe : x ≠ e := fun he => by rw [he, h.root_pre] at hlt; exact Nat.not_lt_zero _ hlt
    obtain ⟨h1, h2, h3, h4⟩ := ih (h.up x hx hxe).1 hy
    refine ⟨h1, .up hxe h2, h3, fun z hzx hzy => h4 z ?_ hzy⟩
    have hzx' : z ≠ x := fun hz => by
      subst hz
      exact absurd (hzy.pre_le h hy) (Nat.not_le.mpr hlt)
    exact (hzx.inv hzx').2
  | case3 x y _ hlt hng =>
    have hxe : x ≠ e := fun he => by rw [he, h.root_pre] at hlt; exact Nat.not_lt_zero _ hlt
    exact absurd (h.up x hx hxe).2 hng
  | case4 x y hne hlt _ ih =>
    have hye : y ≠ e := fun he => by
      subst he
      rw [h.root_pre, Nat.not_lt, Nat.le_zero] at hlt
      exact hne (Classical.byContradiction fun hxe =>
        absurd hlt (Nat.ne_of_gt (h.pre_pos hx hxe)))
    obtain ⟨h1, h2, h3, h4⟩ := ih hx (h.up y hy hye).1
    refine ⟨h1, h2, .up hye h3, fun z hzx hzy => h4 z hzx ?_⟩
    have hzy' : z ≠ y := fun hz => by
      subst hz
      exact hne (hzx.eq_of_pre h hx (Nat.not_lt.mp hlt)).symm
    exact (hzy.inv hzy').2
  | case5 x y hne hlt hng =>
    have hye : y ≠ e := fun he => by
      subst he
      rw [h.root_pre, Nat.not_lt, Nat.le_zero] at hlt
      exact hne (Classical.byContradiction fun hxe =>
        absurd hlt (Nat.ne_of_gt (h.pre_pos hx hxe)))
    exact absurd (h.up y hy hye).2 hng

/-- `nca` folded over a list from `p`: a common ancestor of `p` and of every
block of the list, below every other one. -/
theorem foldl_nca_spec (h : Shaped par pre R e) (L : List Name) (hL : ∀ u ∈ L, R u) {p : Name}
    (hp : R p) :
    R (L.foldl (nca par pre) p) ∧ Ancestor par e (L.foldl (nca par pre) p) p ∧
      (∀ u ∈ L, Ancestor par e (L.foldl (nca par pre) p) u) ∧
      ∀ z, Ancestor par e z p → (∀ u ∈ L, Ancestor par e z u) →
        Ancestor par e z (L.foldl (nca par pre) p) := by
  induction L generalizing p with
  | nil => exact ⟨hp, .refl, fun _ h => by simp at h, fun _ h _ => h⟩
  | cons u L ih =>
    obtain ⟨n1, n2, n3, n4⟩ := nca_spec h hp (hL u (List.mem_cons_self ..))
    obtain ⟨h1, h2, h3, h4⟩ := ih (fun v hv => hL v (List.mem_cons_of_mem _ hv)) n1
    refine ⟨h1, h2.trans n2, ?_, ?_⟩
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact h2.trans n3
      · exact h3 v hv
    · intro z hzp hzL
      exact h4 z (n4 z hzp (hzL u (List.mem_cons_self ..)))
        fun v hv => hzL v (List.mem_cons_of_mem _ hv)

/-! # Paths above a bound -/

/-- A path of the graph `g` from `x` to `y` whose blocks after `x` are all
numbered above `k`. -/
inductive Above (g : Graph) (pre : Name → Nat) (k : Nat) (x : Name) : Name → Prop
  | refl : Above g pre k x x
  | step {y z : Name} : Above g pre k x y → z ∈ g.getD y [] → k < pre z → Above g pre k x z

/-- A path from the entry that avoids the block `z`, as the spec's search
for dominance takes it (`Func.ReachesAvoiding`). -/
abbrev Avoids (g : Graph) (e z y : Name) : Prop := Reach (g.getD · []) (· != z) [e] y

namespace Above

variable {g : Graph}

theorem mono {k k' : Nat} {x y : Name} (hk : k' ≤ k) (h : Above g pre k x y) :
    Above g pre k' x y := by
  induction h with
  | refl => exact .refl
  | step _ hz hp ih => exact .step ih hz (Nat.lt_of_le_of_lt hk hp)

theorem trans {k : Nat} {x y z : Name} (h₁ : Above g pre k x y) (h₂ : Above g pre k y z) :
    Above g pre k x z := by
  induction h₂ with
  | refl => exact h₁
  | step _ hz hp ih => exact .step ih hz hp

/-- A path that avoids `w` up to `x` goes on to `y` along a path whose
blocks are numbered above `w`'s. -/
theorem avoids {k : Nat} {x y w : Name} (h : Above g pre k x y) (hx : Avoids g e w x)
    (hw : pre w ≤ k) : Avoids g e w y := by
  induction h with
  | refl => exact hx
  | step _ hz hp ih =>
    refine .step ih hz ?_
    simp only [bne_iff_ne, ne_eq]
    intro he
    subst he
    exact absurd hp (Nat.not_lt.mpr hw)

end Above

end FirRef.Dom
