import FirRef.Dominance.Ancestor

/-!
`fir-ref` turns the search's spanning tree into the dominator tree by
moving blocks up the tree. The placement of `FirRef.Dominance.Place` moves
each block once, guided by its semidominator. If the tree it ends with
fails the check there, the lifting below goes on: a block whose parent is
not an ancestor of each of its predecessors moves up to the nearest common
ancestor of its parent and its predecessors, and passes over the blocks
repeat until one moves nothing. This is the iterative algorithm of Cooper,
Harvey and Kennedy, which `funk verify` also uses.

Three facts hold of the tree at every step (`Lifted`), and every move that
takes from a block only ancestors that some path avoids keeps them
(`move_lifted`). Each block is
numbered above its parent. Each block is reached from its parent by a path
whose blocks are numbered above the parent. And every block that is not an
ancestor of a block `c` can be avoided on a path from the entry to `c`: so
every dominator of `c` is an ancestor of `c`. When no block moves, each
block's parent is an ancestor of each of its predecessors, so every path
from the entry to a block passes through each of its ancestors
(`Lifted.sound`): the ancestors of a block are exactly its dominators
(`Lifted.ancestor_iff`).

Each move lowers the sum of the numbers of the blocks' parents, so the
passes end; a pass that does not lower it moves nothing.
-/

namespace FirRef.Dom

open Fir

/-- The parent of `x` in the tree `pm`. A block that `pm` gives no parent,
the entry among them, is its own. -/
def parentIn (pm : Std.HashMap Name Name) (x : Name) : Name := pm.getD x x

/-- The predecessors of each block in the graph `g`, among the blocks of
`order`. -/
def preds (g : Graph) (order : List Name) : Std.HashMap Name (List Name) :=
  grouped (order.flatMap fun u => (g.getD u []).map fun y => (y, [u]))

theorem mem_preds {g : Graph} {order : List Name} {u y : Name} :
    u ∈ (preds g order).getD y [] ↔ u ∈ order ∧ y ∈ g.getD u [] := by
  simp only [preds, mem_getD_grouped, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨_, ⟨v, hv, y', hy', rfl⟩, rfl, hu⟩
    rw [List.mem_singleton] at hu
    subst hu
    exact ⟨hv, hy'⟩
  · rintro ⟨hu, hy⟩
    exact ⟨_, ⟨u, hu, y, hy, rfl⟩, rfl, List.mem_singleton_self _⟩

/-- Where block `b` would move: the nearest common ancestor of its parent
and of its predecessors `P`. -/
def target (pre : Name → Nat) (P : Std.HashMap Name (List Name)) (pm : Std.HashMap Name Name)
    (b : Name) : Name :=
  (P.getD b []).foldl (nca (parentIn pm) pre) (parentIn pm b)

/-- Moves block `b` to its target, if that is above its parent. -/
def lift (pre : Name → Nat) (P : Std.HashMap Name (List Name)) (e : Name)
    (pm : Std.HashMap Name Name) (b : Name) : Std.HashMap Name Name :=
  if b = e then pm
  else
    let q := target pre P pm b
    if pre q < pre (parentIn pm b) then pm.insert b q else pm

/-- One pass over the blocks of `order`. -/
def pass (pre : Name → Nat) (P : Std.HashMap Name (List Name)) (e : Name) (order : List Name)
    (pm : Std.HashMap Name Name) : Std.HashMap Name Name :=
  order.foldl (lift pre P e) pm

/-- The sum of the numbers of the parents of the blocks of `order`. -/
def pot (pre : Name → Nat) (order : List Name) (pm : Std.HashMap Name Name) : Nat :=
  order.foldl (fun s x => s + pre (parentIn pm x)) 0

/-- Passes until one moves nothing. -/
def lifts (pre : Name → Nat) (P : Std.HashMap Name (List Name)) (e : Name) (order : List Name)
    (pm : Std.HashMap Name Name) : Std.HashMap Name Name :=
  let pm' := pass pre P e order pm
  if _h : pot pre order pm' < pot pre order pm then lifts pre P e order pm' else pm'
termination_by pot pre order pm

/-- What the lifting is given: the graph `g`, its entry `e`, the reached
blocks `R` with their numbers `pre`, their predecessors `P`, and a list
`order` of them. -/
structure Setting (g : Graph) (e : Name) (pre : Name → Nat) (R : Name → Prop)
    (P : Std.HashMap Name (List Name)) (order : List Name) : Prop where
  root : R e
  root_pre : pre e = 0
  preds : ∀ u y, u ∈ P.getD y [] ↔ R u ∧ y ∈ g.getD u []
  order : ∀ x, x ∈ order ↔ R x
  complete : ∀ (ok : Name → Bool) y, Reach (g.getD · []) ok [e] y → g.contains y = true → R y
  key : ∀ x, R x → g.contains x = true

/-- What holds of the tree `pm` at every step. -/
structure Lifted (g : Graph) (e : Name) (pre : Name → Nat) (R : Name → Prop)
    (pm : Std.HashMap Name Name) : Prop where
  shaped : Shaped (parentIn pm) pre R e
  above : ∀ y, R y → y ≠ e → Above g pre (pre (parentIn pm y)) (parentIn pm y) y
  avoid : ∀ c, R c → ∀ z, z ≠ c → ¬ Ancestor (parentIn pm) e z c → Avoids g e z c

variable {g : Graph} {e : Name} {pre : Name → Nat} {R : Name → Prop}
  {P : Std.HashMap Name (List Name)} {order : List Name}

theorem Lifted.ancestor_above {pm : Std.HashMap Name Name} (h : Lifted g e pre R pm) {x y : Name}
    (hxy : Ancestor (parentIn pm) e x y) (hy : R y) : Above g pre (pre x) x y := by
  induction hxy with
  | refl => exact .refl
  | up hye hxp ih =>
    have hp := h.shaped.up _ hy hye
    exact (ih hp.1).trans ((h.above _ hy hye).mono (hxp.pre_le h.shaped hp.1))

/-- A path that avoids `z` up to `b` goes on to every descendant of `b`, when
`z` is numbered at most `b`. -/
theorem Lifted.avoids_down {pm : Std.HashMap Name Name} (h : Lifted g e pre R pm)
    {z b c : Name} (hb : Avoids g e z b) (hbc : Ancestor (parentIn pm) e b c) (hc : R c)
    (hz : pre z ≤ pre b) : Avoids g e z c :=
  (h.ancestor_above hbc hc).avoids hb hz

/-! # A move keeps the tree's facts -/

section Move

variable {par par' : Name → Name} {b q : Name}

/-- After `b` moves to `q`, an ancestor in the new tree is one in the old. -/
theorem ancestor_of_move (hb : b ≠ e) (hq : Ancestor par e q (par b))
    (hpar : ∀ y, y ≠ b → par' y = par y) (hpb : par' b = q) {x y : Name}
    (h : Ancestor par' e x y) : Ancestor par e x y := by
  induction h with
  | refl => exact .refl
  | @up y hye _ ih =>
    by_cases hyb : y = b
    · subst hyb
      rw [hpb] at ih
      exact .up hye (ih.trans hq)
    · rw [hpar y hyb] at ih
      exact .up hye ih

/-- Below `b`'s number, the old tree's ancestors are the new tree's. -/
theorem ancestor_move_below (hs : Shaped par pre R e) (hpar : ∀ y, y ≠ b → par' y = par y)
    {x y : Name} (h : Ancestor par e x y) (hy : R y) (hlt : pre y < pre b) :
    Ancestor par' e x y := by
  induction h with
  | refl => exact .refl
  | @up y hye _ ih =>
    have hyb : y ≠ b := fun h' => by rw [h'] at hlt; exact Nat.lt_irrefl _ hlt
    have hp := hs.up y hy hye
    exact .up hye (by rw [hpar y hyb]; exact ih hp.1 (Nat.lt_trans hp.2 hlt))

/-- An ancestor that the move loses is an ancestor of `b`'s old parent that
is not one of `q`, above a block that `b` is an ancestor of in the new tree. -/
theorem ancestor_lost (hs : Shaped par pre R e) (hpar : ∀ y, y ≠ b → par' y = par y)
    (hpb : par' b = q) (hb : b ≠ e) (hqR : R q) (hqb : pre q < pre b) {x y : Name}
    (h : Ancestor par e x y) (hn : ¬ Ancestor par' e x y) :
    Ancestor par e x (par b) ∧ ¬ Ancestor par e x q ∧ Ancestor par' e b y ∧ x ≠ b := by
  induction h with
  | refl => exact absurd .refl hn
  | @up y hye hxp ih =>
    by_cases hyb : y = b
    · subst hyb
      refine ⟨hxp, fun hxq => hn (.up hye ?_), .refl, fun hx => hn (hx ▸ .refl)⟩
      rw [hpb]
      exact ancestor_move_below hs hpar hxq hqR hqb
    · have hn' : ¬ Ancestor par' e x (par y) :=
        fun h' => hn (.up hye (by rw [hpar y hyb]; exact h'))
      obtain ⟨h1, h2, h3, h4⟩ := ih hn'
      exact ⟨h1, h2, .up hye (by rw [hpar y hyb]; exact h3), h4⟩

end Move

theorem parentIn_insert (pm : Std.HashMap Name Name) (b q y : Name) :
    parentIn (pm.insert b q) y = if b = y then q else parentIn pm y := by
  simp [parentIn, Std.HashMap.getD_insert]

/-- Moving block `b` up to an ancestor `q` of its parent keeps the tree's
facts, when every block that the move takes from `b`'s ancestors can be
avoided on a path from the entry to `b`. -/
theorem move_lifted {pm : Std.HashMap Name Name} (h : Lifted g e pre R pm) {b q : Name}
    (hb : R b) (hbe : b ≠ e) (hq : Ancestor (parentIn pm) e q (parentIn pm b))
    (hlost : ∀ z, Ancestor (parentIn pm) e z (parentIn pm b) → ¬ Ancestor (parentIn pm) e z q →
      z ≠ b → Avoids g e z b) :
    Lifted g e pre R (pm.insert b q) := by
  have hs := h.shaped
  have hp := hs.up b hb hbe
  have hqR : R q := hq.mem hs hp.1
  have hpar : ∀ y, y ≠ b → parentIn (pm.insert b q) y = parentIn pm y :=
    fun y hy => by rw [parentIn_insert, ite_eq_right (Ne.symm hy)]
  have hpb : parentIn (pm.insert b q) b = q := by rw [parentIn_insert, ite_eq_left rfl]
  have hqp := hq.pre_le hs hp.1
  have hqb : pre q < pre b := Nat.lt_of_le_of_lt hqp hp.2
  refine ⟨⟨hs.root, hs.root_pre, ?_⟩, ?_, ?_⟩
  · intro y hy hye
    by_cases hyb : y = b
    · subst hyb; rw [hpb]; exact ⟨hqR, hqb⟩
    · rw [hpar y hyb]; exact hs.up y hy hye
  · intro y hy hye
    by_cases hyb : y = b
    · subst hyb
      rw [hpb]
      exact (h.ancestor_above hq hp.1).trans ((h.above y hb hye).mono hqp)
    · rw [hpar y hyb]; exact h.above y hy hye
  · intro c hc z hzc hn
    by_cases hzc' : Ancestor (parentIn pm) e z c
    · obtain ⟨h1, h2, h3, h4⟩ := ancestor_lost hs hpar hpb hbe hqR hqb hzc' hn
      exact h.avoids_down (hlost z h1 h2 h4) (ancestor_of_move hbe hq hpar hpb h3) hc
        (Nat.le_of_lt (Nat.lt_of_le_of_lt (h1.pre_le hs hp.1) hp.2))
    · exact h.avoid c hc z hzc hzc'

theorem lift_lifted (S : Setting g e pre R P order) {pm : Std.HashMap Name Name}
    (h : Lifted g e pre R pm) {b : Name} (hb : R b) : Lifted g e pre R (lift pre P e pm b) := by
  unfold lift
  split
  · exact h
  rename_i hbe
  simp only
  split
  · have hp := h.shaped.up b hb hbe
    obtain ⟨_, n2, _, n4⟩ := foldl_nca_spec h.shaped (P.getD b [])
      (fun u hu => ((S.preds u b).mp hu).1) hp.1
    refine move_lifted h hb hbe n2 fun z h1 h2 h4 => ?_
    have : ¬ ∀ u ∈ P.getD b [], Ancestor (parentIn pm) e z u := fun hall => h2 (n4 z h1 hall)
    obtain ⟨u, hzu⟩ := Classical.not_forall.mp this
    obtain ⟨hu, hzu⟩ := Classical.not_imp.mp hzu
    obtain ⟨huR, hub⟩ := (S.preds u b).mp hu
    have hzu' : z ≠ u := fun h' => hzu (h' ▸ .refl)
    exact .step (h.avoid u huR z hzu' hzu) hub (bne_iff_ne.mpr h4.symm)
  · exact h

theorem pass_lifted (S : Setting g e pre R P order) (L : List Name) (hL : ∀ b ∈ L, R b)
    {pm : Std.HashMap Name Name} (h : Lifted g e pre R pm) :
    Lifted g e pre R (L.foldl (lift pre P e) pm) := by
  induction L generalizing pm with
  | nil => exact h
  | cons b L ih =>
    exact ih (fun b' hb' => hL b' (List.mem_cons_of_mem _ hb'))
      (lift_lifted S h (hL b (List.mem_cons_self ..)))

/-! # The passes end -/

theorem foldl_add_le {f f' : Name → Nat} (hf : ∀ x, f' x ≤ f x) (L : List Name) {s s' : Nat}
    (hs : s' ≤ s) : L.foldl (fun t x => t + f' x) s' ≤ L.foldl (fun t x => t + f x) s := by
  induction L generalizing s s' with
  | nil => exact hs
  | cons x L ih => exact ih (Nat.add_le_add hs (hf x))

theorem foldl_add_shift (f : Name → Nat) (L : List Name) (s k : Nat) :
    L.foldl (fun t x => t + f x) (s + k) = L.foldl (fun t x => t + f x) s + k := by
  induction L generalizing s with
  | nil => rfl
  | cons x L ih =>
    simp only [List.foldl_cons]
    rw [Nat.add_right_comm, ih]

theorem foldl_add_lt {f f' : Name → Nat} (hf : ∀ x, f' x ≤ f x) {L : List Name} {b : Name}
    (hb : b ∈ L) (hlt : f' b < f b) {s s' : Nat} (hs : s' ≤ s) :
    L.foldl (fun t x => t + f' x) s' < L.foldl (fun t x => t + f x) s := by
  induction L generalizing s s' with
  | nil => simp at hb
  | cons x L ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hb with rfl | hb
    · rw [foldl_add_shift, foldl_add_shift]
      exact Nat.lt_of_le_of_lt (Nat.add_le_add_right (foldl_add_le hf L hs) _)
        (Nat.add_lt_add_left hlt _)
    · exact ih hb (Nat.add_le_add hs (hf x))

/-- Whether block `b` moves in the tree `pm`. -/
def Fires (pre : Name → Nat) (P : Std.HashMap Name (List Name)) (e : Name)
    (pm : Std.HashMap Name Name) (b : Name) : Prop :=
  b ≠ e ∧ pre (target pre P pm b) < pre (parentIn pm b)

theorem lift_of_not_fires {pm : Std.HashMap Name Name} {b : Name} (h : ¬ Fires pre P e pm b) :
    lift pre P e pm b = pm := by
  unfold lift Fires at *
  split
  · rfl
  · rename_i hbe
    simp only
    rw [ite_eq_right fun hlt => h ⟨hbe, hlt⟩]

theorem pot_lift_lt {pm : Std.HashMap Name Name} {b : Name} (hb : b ∈ order)
    (h : Fires pre P e pm b) : pot pre order (lift pre P e pm b) < pot pre order pm := by
  unfold lift
  rw [ite_eq_right h.1]
  simp only
  rw [ite_eq_left h.2]
  unfold pot
  apply foldl_add_lt (b := b) _ hb _ (Nat.le_refl _)
  · intro x
    rw [parentIn_insert]
    split
    · rename_i hx; subst hx; exact Nat.le_of_lt h.2
    · exact Nat.le_refl _
  · rw [parentIn_insert, ite_eq_left rfl]; exact h.2

/-- A pass lowers the sum, or moves nothing. -/
theorem pot_pass (L : List Name) (hL : ∀ b ∈ L, b ∈ order) (pm : Std.HashMap Name Name) :
    pot pre order (L.foldl (lift pre P e) pm) ≤ pot pre order pm ∧
      (pot pre order (L.foldl (lift pre P e) pm) = pot pre order pm →
        L.foldl (lift pre P e) pm = pm ∧ ∀ b ∈ L, ¬ Fires pre P e pm b) := by
  induction L generalizing pm with
  | nil => exact ⟨Nat.le_refl _, fun _ => ⟨rfl, fun _ h => by simp at h⟩⟩
  | cons b L ih =>
    simp only [List.foldl_cons]
    have ih' := ih (fun b' hb' => hL b' (List.mem_cons_of_mem _ hb'))
    by_cases hf : Fires pre P e pm b
    · have hlt := pot_lift_lt (hL b (List.mem_cons_self ..)) hf
      have hle := (ih' (lift pre P e pm b)).1
      exact ⟨Nat.le_of_lt (Nat.lt_of_le_of_lt hle hlt),
        fun heq => absurd (heq ▸ Nat.lt_of_le_of_lt hle hlt) (Nat.lt_irrefl _)⟩
    · rw [lift_of_not_fires hf]
      obtain ⟨h1, h2⟩ := ih' pm
      refine ⟨h1, fun heq => ⟨(h2 heq).1, fun b' hb' => ?_⟩⟩
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact hf
      · exact (h2 heq).2 b' hb'

/-- What the passes end with: a tree with the facts above, in which each
block's parent is an ancestor of each of its predecessors. -/
theorem lifts_spec (S : Setting g e pre R P order) {pm : Std.HashMap Name Name}
    (h : Lifted g e pre R pm) :
    Lifted g e pre R (lifts pre P e order pm) ∧
      ∀ b, R b → b ≠ e → ∀ u ∈ P.getD b [],
        Ancestor (parentIn (lifts pre P e order pm)) e (parentIn (lifts pre P e order pm) b) u := by
  have hR : ∀ b ∈ order, R b := fun b hb => (S.order b).mp hb
  fun_induction lifts pre P e order pm with
  | case1 pm _ _ ih => exact ih (pass_lifted S order hR h)
  | case2 pm _ hng =>
    have hng' : ¬ pot pre order (pass pre P e order pm) < pot pre order pm := hng
    show Lifted g e pre R (pass pre P e order pm) ∧ ∀ b, R b → b ≠ e → ∀ u ∈ P.getD b [],
      Ancestor (parentIn (pass pre P e order pm)) e (parentIn (pass pre P e order pm) b) u
    obtain ⟨hle, heq⟩ := pot_pass (pre := pre) (P := P) (e := e) order (fun _ hb => hb) pm
    obtain ⟨hfix, hno⟩ := heq (Nat.le_antisymm hle (Nat.not_lt.mp hng'))
    unfold pass
    rw [hfix]
    refine ⟨h, fun b hb hbe u hu => ?_⟩
    have hs := h.shaped
    have hp := hs.up b hb hbe
    obtain ⟨_, n2, n3, _⟩ := foldl_nca_spec hs (P.getD b [])
      (fun u hu => ((S.preds u b).mp hu).1) hp.1
    have heq' := n2.eq_of_pre hs hp.1
      (Nat.not_lt.mp fun hlt => hno b ((S.order b).mpr hb) ⟨hbe, hlt⟩)
    unfold target at heq'
    rw [← heq']
    exact n3 u hu

/-! # The ancestors are the dominators -/

/-- When each block's parent is an ancestor of each of its predecessors, no
path from the entry to a block avoids one of its ancestors. -/
theorem Lifted.sound (S : Setting g e pre R P order) {par : Name → Name}
    (hfix : ∀ b, R b → b ≠ e → ∀ u ∈ P.getD b [], Ancestor par e (par b) u) {z y : Name}
    (hy : Avoids g e z y) (hg : g.contains y = true) : ¬ Ancestor par e z y := by
  induction hy with
  | start hx hok =>
    rw [List.mem_singleton] at hx
    subst hx
    intro ha
    rw [ha.root, bne_self_eq_false] at hok
    exact Bool.false_ne_true hok
  | @step x y hx hy hok ih =>
    intro ha
    have hzy : z ≠ y := fun h' => by rw [h', bne_self_eq_false] at hok; exact Bool.false_ne_true hok
    obtain ⟨hye, hzp⟩ := ha.inv hzy
    have hgx : g.contains x = true := by
      apply Classical.byContradiction
      intro hn
      rw [Std.HashMap.getD_eq_fallback (by simpa using hn)] at hy
      simp at hy
    have hyR := S.complete _ y (.step hx hy hok) hg
    have hxR := S.complete _ x hx hgx
    exact ih hgx (hzp.trans (hfix y hyR hye x ((S.preds x y).mpr ⟨hxR, hy⟩)))

/-- In the tree the passes end with, a block's ancestors are its
dominators. -/
theorem Lifted.ancestor_iff (S : Setting g e pre R P order) {pm : Std.HashMap Name Name}
    (h : Lifted g e pre R pm)
    (hfix : ∀ b, R b → b ≠ e → ∀ u ∈ P.getD b [], Ancestor (parentIn pm) e (parentIn pm b) u)
    {z c : Name} (hc : R c) : Ancestor (parentIn pm) e z c ↔ (z = c ∨ ¬ Avoids g e z c) := by
  constructor
  · intro ha
    by_cases hzc : z = c
    · exact .inl hzc
    · exact .inr fun hpath => Lifted.sound S hfix hpath (S.key c hc) ha
  · rintro (rfl | hn)
    · exact .refl
    · exact Classical.byContradiction fun ha =>
        hn (h.avoid c hc z (fun h' => ha (h' ▸ .refl)) ha)

end FirRef.Dom
