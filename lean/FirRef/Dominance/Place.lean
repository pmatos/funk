import FirRef.Dominance.Jump
import FirRef.Dominance.Semi

/-!
The placement of the semi-NCA algorithm (L. Georgiadis, "Linear-time
algorithms for dominators and related problems", 2005; Georgiadis, Tarjan
and Werneck, "Finding dominators in practice", 2006). The blocks are taken
in increasing order of their numbers in the search's tree, and each moves
from its tree parent up to the nearest ancestor of that parent numbered at
most its semidominator. When the semidominators are exact, that ancestor is
the block's immediate dominator. The tree grows from the entry down, so the
blocks above a block are placed for good before it, and each placed block
gets its jump pointer at once: a walk up takes steps logarithmic in the
depth (`upTo`).

The proofs need no theory of semidominators. Each move keeps the facts of
`Lifted` (`Placing.add_ok`): a block that the move takes from the ancestors
of `v` is numbered above `v`'s semidominator `s`, so it is not an ancestor
of `s`; a path from the entry reaches `s` without it, and `s`'s path then
reaches `v`. Whether the tree is the dominator tree is then a check of
each block's parent against its predecessors (`fixed`), with the jump
pointers, in steps logarithmic in the depth per edge.
-/

namespace FirRef.Dom

open Fir

/-- The placement so far: the tree, the jump pointers of the blocks placed,
and the highest number placed. -/
structure Placing where
  pm : Std.HashMap Name Name
  js : Jumps
  hi : Nat

/-- Places block `v`, given the semidominators `sem`. A block numbered no
higher than one placed already is skipped, so the proofs need no order. -/
def Placing.add (pre : Name → Nat) (sem : Name → Name) (e : Name) : Placing → Name → Placing
  | ⟨pm, js, hi⟩, v =>
    if v ≠ e ∧ hi < pre v then
      let p := parentIn pm v
      let q := upTo pre (parentIn pm) (parentIn js.jump) (pre (sem v)) p
      let pm := if pre q < pre p then pm.insert v q else pm
      ⟨pm, Jumps.add pm e js v, pre v⟩
    else ⟨pm, js, hi⟩

/-- Places the blocks of `order`, from the tree `pm`. -/
def place (pre : Name → Nat) (sem : Name → Name) (e : Name) (order : List Name)
    (pm : Std.HashMap Name Name) : Placing :=
  order.foldl (Placing.add pre sem e) ⟨pm, ⟨∅, ∅⟩, 0⟩

/-- Whether each block's parent in `pm` is an ancestor of each of its
predecessors, asked with the jump pointers `jump`. -/
def fixed (pre : Name → Nat) (P : Std.HashMap Name (List Name)) (e : Name)
    (pm jump : Std.HashMap Name Name) (order : List Name) : Bool :=
  order.all fun b => b == e ||
    (P.getD b []).all fun u => climbs pre (parentIn pm) (parentIn jump) (parentIn pm b) u

variable {g : Graph} {e : Name} {pre : Name → Nat} {R : Name → Prop}

/-- What holds of the placement at every step: the tree has the facts of
`Lifted`, every jump pointer is an ancestor, and only blocks numbered at
most `hi` have one. -/
structure Placing.Ok (g : Graph) (e : Name) (pre : Name → Nat) (R : Name → Prop)
    (st : Placing) : Prop where
  lifted : Lifted g e pre R st.pm
  jump : ∀ x, R x → Ancestor (parentIn st.pm) e (parentIn st.js.jump x) x ∧
    R (parentIn st.js.jump x)
  hi : ∀ x, st.js.jump.contains x = true → pre x ≤ st.hi

theorem Placing.add_ok {sem : Name → Name}
    (hsem : ∀ x, R x → R (sem x) ∧ Above g pre (pre x - 1) (sem x) x) {st : Placing}
    (h : st.Ok g e pre R) {v : Name} (hv : R v) : (Placing.add pre sem e st v).Ok g e pre R := by
  obtain ⟨pm, js, hi⟩ := st
  obtain ⟨hl, hj, hh⟩ := h
  dsimp only at hl hj hh
  simp only [Placing.add]
  split
  · rename_i hc
    obtain ⟨hvne, hlt⟩ := hc
    have hs := hl.shaped
    have hp := hs.up v hv hvne
    obtain ⟨hsR, hsv⟩ := hsem v hv
    obtain ⟨q1, q2, q3⟩ := upTo_spec hs hj (pre (sem v)) hp.1
    generalize upTo pre (parentIn pm) (parentIn js.jump) (pre (sem v)) (parentIn pm v) = q
      at q1 q2 q3 ⊢
    have hlost : ∀ z, Ancestor (parentIn pm) e z (parentIn pm v) →
        ¬ Ancestor (parentIn pm) e z q → z ≠ v → Avoids g e z v := by
      intro z hz1 hz2 _
      have hk := q3 z hz1 hz2
      have hzs : ¬ Ancestor (parentIn pm) e z (sem v) := fun h' =>
        absurd (h'.pre_le hs hsR) (Nat.not_le.mpr hk)
      have hzs' : z ≠ sem v := fun h' => hzs (h' ▸ .refl)
      have hzp := hz1.pre_le hs hp.1
      have := hp.2
      exact (hsv.mono (by omega)).avoids (hl.avoid _ hsR z hzs' hzs) (Nat.le_refl _)
    have htree : Lifted g e pre R (if pre q < pre (parentIn pm v) then pm.insert v q else pm) ∧
        ∀ y, y ≠ v →
          parentIn (if pre q < pre (parentIn pm v) then pm.insert v q else pm) y = parentIn pm y := by
      split
      · exact ⟨move_lifted hl hv hvne q2 hlost,
          fun y hy => by rw [parentIn_insert, ite_eq_right (Ne.symm hy)]⟩
      · exact ⟨hl, fun _ _ => rfl⟩
    generalize (if pre q < pre (parentIn pm v) then pm.insert v q else pm) = pm' at htree ⊢
    obtain ⟨hl', hpar⟩ := htree
    have hj' : ∀ x, R x → Ancestor (parentIn pm') e (parentIn js.jump x) x ∧
        R (parentIn js.jump x) := by
      intro x hx
      cases hc : js.jump.contains x
      · simp only [parentIn, Std.HashMap.getD_eq_fallback_of_contains_eq_false hc]
        exact ⟨.refl, hx⟩
      · obtain ⟨a1, r1⟩ := hj x hx
        exact ⟨ancestor_move_below hs hpar a1 hx (Nat.lt_of_le_of_lt (hh x hc) hlt), r1⟩
    refine ⟨hl', Jumps.add_ancestor rfl hl'.shaped hv hj', fun x hx => ?_⟩
    dsimp only at hx ⊢
    unfold Jumps.add at hx
    rw [ite_eq_right hvne] at hx
    simp only [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with rfl | hx
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hh x hx) hlt)
  · exact ⟨hl, hj, hh⟩

/-- The placement of every block of `order` keeps the facts of `Lifted`. -/
theorem place_ok {sem : Name → Name}
    (hsem : ∀ x, R x → R (sem x) ∧ Above g pre (pre x - 1) (sem x) x)
    {pm : Std.HashMap Name Name} (h : Lifted g e pre R pm) (order : List Name)
    (hord : ∀ x ∈ order, R x) : (place pre sem e order pm).Ok g e pre R := by
  unfold place
  suffices ∀ (L : List Name) (st : Placing), (∀ x ∈ L, R x) → st.Ok g e pre R →
      (L.foldl (Placing.add pre sem e) st).Ok g e pre R from
    this order _ hord ⟨h, fun x hx => by
      simp only [parentIn, Std.HashMap.getD_empty]; exact ⟨.refl, hx⟩,
      fun x hx => by simp at hx⟩
  intro L
  induction L with
  | nil => exact fun _ _ h => h
  | cons v L ih =>
    exact fun st hL h => ih _ (fun x hx => hL x (List.mem_cons_of_mem _ hx))
      (Placing.add_ok hsem h (hL v (List.mem_cons_self ..)))

/-- When the check passes, each block's parent is an ancestor of each of
its predecessors. -/
theorem fixed_spec {P : Std.HashMap Name (List Name)} {order : List Name}
    (S : Setting g e pre R P order) {pm jump : Std.HashMap Name Name}
    (hs : Shaped (parentIn pm) pre R e)
    (hj : ∀ x, R x → Ancestor (parentIn pm) e (parentIn jump x) x ∧ R (parentIn jump x))
    (hf : fixed pre P e pm jump order = true) :
    ∀ b, R b → b ≠ e → ∀ u ∈ P.getD b [], Ancestor (parentIn pm) e (parentIn pm b) u := by
  intro b hb hbe u hu
  have h1 := List.all_eq_true.mp hf b ((S.order b).mpr hb)
  rw [beq_eq_false_iff_ne.mpr hbe, Bool.false_or] at h1
  exact (climbs_iff hs hj ((S.preds u b).mp hu).1).mp (List.all_eq_true.mp h1 u hu)

end FirRef.Dom
