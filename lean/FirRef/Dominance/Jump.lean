import FirRef.Dominance.Lift

/-!
Walks up a tree in steps logarithmic in its depth. Each block has a jump
pointer, an ancestor chosen by the rule of Myers' skew-binary lists (E. W.
Myers, "An applicative random-access stack", 1983); the proofs need only
that it is an ancestor. A walk takes a block's jump pointer when that does
not pass what it looks for, and its parent otherwise. `climbs` decides
whether a block is an ancestor of another; `upTo` finds a block's nearest
ancestor numbered at most a bound. Both check the numbers they read, so
they end on any input; on a shaped tree the checks always pass.
-/

namespace FirRef.Dom

open Fir

variable {e : Name}

/-! # Jump pointers -/

/-- The jump pointer and the depth of each block given one so far. -/
structure Jumps where
  jump : Std.HashMap Name Name
  depth : Std.HashMap Name Nat

/-- Gives block `x` of the tree `pm` its jump pointer: its parent's jump
pointer's jump pointer, when the parent's two jumps are equally long, or
else its parent. -/
def Jumps.add (pm : Std.HashMap Name Name) (e : Name) (j : Jumps) (x : Name) : Jumps :=
  if x = e then j
  else
    let p := parentIn pm x
    let jp := parentIn j.jump p
    let jjp := parentIn j.jump jp
    let dp := j.depth.getD p 0
    let djp := j.depth.getD jp 0
    let v := if dp - djp = djp - j.depth.getD jjp 0 then jjp else p
    ⟨j.jump.insert x v, j.depth.insert x (dp + 1)⟩

/-- The jump pointers of the blocks of `order`, parents first. -/
def jumps (pm : Std.HashMap Name Name) (e : Name) (order : List Name) : Jumps :=
  order.foldl (Jumps.add pm e) ⟨∅, ∅⟩

/-- Giving block `y` its jump pointer keeps every jump pointer an ancestor. -/
theorem Jumps.add_ancestor {par : Name → Name} {pre : Name → Nat} {R : Name → Prop}
    {pm : Std.HashMap Name Name} (hpar : par = parentIn pm) (hs : Shaped par pre R e)
    {j : Jumps} {y : Name} (hy : R y)
    (hj : ∀ x, R x → Ancestor par e (parentIn j.jump x) x ∧ R (parentIn j.jump x)) :
    ∀ x, R x → Ancestor par e (parentIn (Jumps.add pm e j y).jump x) x ∧
      R (parentIn (Jumps.add pm e j y).jump x) := by
  intro x hx
  unfold Jumps.add
  split
  · exact hj x hx
  · rename_i hye
    simp only
    rw [parentIn_insert]
    split
    · rename_i hyx
      subst hyx
      have hp := hs.up _ hy hye
      rw [hpar] at hp
      obtain ⟨a1, r1⟩ := hj _ hp.1
      obtain ⟨a2, r2⟩ := hj _ r1
      have hup : Ancestor par e (parentIn pm y) y := .up hye (hpar ▸ .refl)
      split
      · exact ⟨(a2.trans a1).trans hup, r2⟩
      · exact ⟨hup, hp.1⟩
    · exact hj x hx

theorem jumps_ancestor {par : Name → Name} {pre : Name → Nat} {R : Name → Prop}
    {pm : Std.HashMap Name Name} (hpar : par = parentIn pm) (hs : Shaped par pre R e)
    (order : List Name) (hord : ∀ x ∈ order, R x) :
    ∀ x, R x → Ancestor par e (parentIn (jumps pm e order).jump x) x ∧
      R (parentIn (jumps pm e order).jump x) := by
  suffices ∀ (L : List Name) (j : Jumps), (∀ x ∈ L, R x) →
      (∀ x, R x → Ancestor par e (parentIn j.jump x) x ∧ R (parentIn j.jump x)) →
      ∀ x, R x → Ancestor par e (parentIn (L.foldl (Jumps.add pm e) j).jump x) x ∧
        R (parentIn (L.foldl (Jumps.add pm e) j).jump x) from
    this order _ hord fun x hx => by
      simp only [parentIn, Std.HashMap.getD_empty]; exact ⟨.refl, hx⟩
  intro L
  induction L with
  | nil => exact fun _ _ h => h
  | cons y L ih =>
    intro j hL hj
    exact ih _ (fun x hx => hL x (List.mem_cons_of_mem _ hx))
      (Jumps.add_ancestor hpar hs (hL y (List.mem_cons_self ..)) hj)

/-! # The walks -/

/-- Whether `a` is an ancestor of `cur`: walk up from `cur`, by jump
pointers that do not pass `a`'s number and otherwise by parents, until the
number is at most `a`'s. -/
def climbs (pre : Name → Nat) (par jump : Name → Name) (a cur : Name) : Bool :=
  if pre cur ≤ pre a then decide (cur = a)
  else if pre a ≤ pre (jump cur) ∧ pre (jump cur) < pre cur then climbs pre par jump a (jump cur)
  else if pre (par cur) < pre cur then climbs pre par jump a (par cur)
  else false
termination_by pre cur

theorem climbs_iff {par jump : Name → Name} {pre : Name → Nat} {R : Name → Prop}
    (hs : Shaped par pre R e) (hj : ∀ x, R x → Ancestor par e (jump x) x ∧ R (jump x))
    {a cur : Name} (hc : R cur) : climbs pre par jump a cur = true ↔ Ancestor par e a cur := by
  fun_induction climbs pre par jump a cur with
  | case1 cur hle =>
    rw [decide_eq_true_iff]
    exact ⟨fun h => h ▸ .refl, fun h => (h.eq_of_pre hs hc hle).symm⟩
  | case2 cur _ hj' ih =>
    obtain ⟨ha, hr⟩ := hj cur hc
    rw [ih hr]
    refine ⟨fun h => h.trans ha, fun h => ?_⟩
    rcases h.linear ha with h' | h'
    · exact h'
    · exact (h'.eq_of_pre hs (h.mem hs hc) hj'.1) ▸ .refl
  | case3 cur hgt _ hlt ih =>
    have hce : cur ≠ e := fun he => by
      rw [he, hs.root_pre] at hgt; exact hgt (Nat.zero_le _)
    rw [ih (hs.up cur hc hce).1]
    refine ⟨fun h => .up hce h, fun h => (h.inv fun h' => hgt (h' ▸ Nat.le_refl _)).2⟩
  | case4 cur hgt _ hng =>
    have hce : cur ≠ e := fun he => by
      rw [he, hs.root_pre] at hgt; exact hgt (Nat.zero_le _)
    exact absurd (hs.up cur hc hce).2 hng

/-- The nearest ancestor of `cur` numbered at most `k`: walk up from `cur`,
by jump pointers that stay above `k` and otherwise by parents. -/
def upTo (pre : Name → Nat) (par jump : Name → Name) (k : Nat) (cur : Name) : Name :=
  if pre cur ≤ k then cur
  else if k < pre (jump cur) ∧ pre (jump cur) < pre cur then upTo pre par jump k (jump cur)
  else if pre (par cur) < pre cur then upTo pre par jump k (par cur)
  else cur
termination_by pre cur

/-- What `upTo` finds: an ancestor of `cur`, above which every ancestor of
`cur` is numbered above `k`. -/
theorem upTo_spec {par jump : Name → Name} {pre : Name → Nat} {R : Name → Prop}
    (hs : Shaped par pre R e) (hj : ∀ x, R x → Ancestor par e (jump x) x ∧ R (jump x))
    (k : Nat) {cur : Name} (hc : R cur) :
    R (upTo pre par jump k cur) ∧ Ancestor par e (upTo pre par jump k cur) cur ∧
      ∀ z, Ancestor par e z cur → ¬ Ancestor par e z (upTo pre par jump k cur) → k < pre z := by
  fun_induction upTo pre par jump k cur with
  | case1 cur _ => exact ⟨hc, .refl, fun _ hz hn => absurd hz hn⟩
  | case2 cur _ hj' ih =>
    obtain ⟨ha, hr⟩ := hj cur hc
    obtain ⟨i1, i2, i3⟩ := ih hr
    refine ⟨i1, i2.trans ha, fun z hz hn => ?_⟩
    rcases hz.linear ha with h' | h'
    · exact i3 z h' hn
    · exact Nat.lt_of_lt_of_le hj'.1 (h'.pre_le hs (hz.mem hs hc))
  | case3 cur hgt _ _ ih =>
    have hce : cur ≠ e := fun he => by
      rw [he, hs.root_pre] at hgt; exact hgt (Nat.zero_le _)
    obtain ⟨i1, i2, i3⟩ := ih (hs.up cur hc hce).1
    refine ⟨i1, .up hce i2, fun z hz hn => ?_⟩
    by_cases hzc : z = cur
    · subst hzc; exact Nat.lt_of_not_le hgt
    · exact i3 z (hz.inv hzc).2 hn
  | case4 cur hgt _ hng =>
    have hce : cur ≠ e := fun he => by
      rw [he, hs.root_pre] at hgt; exact hgt (Nat.zero_le _)
    exact absurd (hs.up cur hc hce).2 hng

end FirRef.Dom
