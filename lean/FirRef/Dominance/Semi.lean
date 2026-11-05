import FirRef.Dominance.Lift

/-!
Semidominators, by the simple version of Lengauer and Tarjan's algorithm
(T. Lengauer and R. E. Tarjan, "A fast algorithm for finding dominators in
a flowgraph", 1979): path compression without balancing, `O(m log n)`
steps for `n` blocks and `m` edges. The blocks are done in decreasing
order of their numbers in the search's tree. A block's semidominator is
the lowest-numbered of its candidates: each predecessor numbered below it,
and the semidominator of each done block on the tree path down to each
other predecessor. A forest over the done blocks, whose paths are
compressed as they are walked, finds the lowest of those.

The proofs need less than that. They need only that the block `semi v`
chosen for `v` reaches `v` along a path whose blocks after `semi v` are
numbered at least as high as `v` (`Semis.Ok`). Every candidate has such a
path, whichever the algorithm picks: the predecessor by its edge, and the
semidominator of a done block by its own path, then the tree path down to
the predecessor, then the edge. That the pick is the true semidominator is
what makes the placement of `FirRef.Dominance.Place` the dominator tree;
the check there confirms it.

Each map holds only what differs from its default, so a chain of blocks
costs no insertion. A done block's default forest parent is its tree
parent, its default label is itself, and its default semidominator is its
tree parent; a block not done is its own semidominator. Every walk is a
tail call or a fold, so the computation takes no stack per block.
-/

namespace FirRef.Dom

open Fir

/-- What the computation keeps: the blocks numbered at least `lo` are done,
and the maps hold their semidominators, forest parents and labels where
these differ from their defaults. -/
structure Semis where
  sd : Std.HashMap Name Name
  links : Std.HashMap Name Name
  lab : Std.HashMap Name Name
  lo : Nat

namespace Semis

section

variable (pre : Name → Nat) (tp : Name → Name)

/-- A done block's parent in the forest. -/
def up (s : Semis) (x : Name) : Name := s.links.getD x (tp x)

/-- A done block's label: a block on its forest path with the lowest
semidominator found. -/
def label (s : Semis) (x : Name) : Name := s.lab.getD x x

/-- A block's semidominator so far. -/
def semi (s : Semis) (x : Name) : Name := s.sd.getD x (if s.lo ≤ pre x then tp x else x)

/-- The done blocks from `x` up the forest whose forest parents are done
too, the highest first: the blocks whose links a compression shortens. -/
def chain (s : Semis) (x : Name) (acc : List Name) : List Name :=
  if s.lo ≤ pre (s.up tp x) ∧ pre (s.up tp x) < pre x then chain s (s.up tp x) (x :: acc)
  else acc
termination_by pre x

/-- `lab` with the label of `x` set to `la`, when `lower`. -/
def relabel (lab : Std.HashMap Name Name) (x la : Name) : Bool → Std.HashMap Name Name
  | true => lab.insert x la
  | false => lab

/-- Shortens the link of the done block `x` past its forest parent `a`,
when `a` is done: `x` links to `a`'s forest parent, and takes `a`'s label
when that has the lower semidominator. -/
def squash (s : Semis) (x : Name) : Semis :=
  let a := s.up tp x
  if s.lo ≤ pre x ∧ s.lo ≤ pre a then
    let r := s.up tp a
    let la := s.label a
    let lower := decide (pre (s.semi pre tp la) < pre (s.semi pre tp (s.label x)))
    match s with
    | ⟨sd, links, lab, lo⟩ => ⟨sd, links.insert x r, relabel lab x la lower, lo⟩
  else s

/-- The label of `u` after its forest path is compressed, or `u` itself
when it is not done. -/
def eval (s : Semis) (u : Name) : Semis × Name :=
  if s.lo ≤ pre u then
    let s := (chain pre tp s u []).foldl (squash pre tp) s
    (s, s.label u)
  else (s, u)

/-- The candidate that the predecessor `u` offers, against the lowest so
far. -/
def offer : Semis × Name → Name → Semis × Name
  | (s, best), u =>
    match s.eval pre tp u with
    | (s, w) =>
      let c := s.semi pre tp w
      (s, if pre c < pre best then c else best)

/-- Does block `v`: its semidominator is the lowest candidate of its
predecessors `P`, and it joins the forest. A block numbered at least as
high as one done already is skipped, so the proofs need no order. -/
def visit (P : Std.HashMap Name (List Name)) (e : Name) (s : Semis) (v : Name) : Semis :=
  if v ≠ e ∧ pre v < s.lo then
    match (P.getD v []).foldl (offer pre tp) (s, tp v) with
    | (⟨sd, links, lab, _⟩, best) =>
      ⟨if pre best < pre (tp v) then sd.insert v best else sd, links, lab, pre v⟩
  else s

end

/-- The semidominators of the blocks of `order`, done in that order, with
the blocks numbered `n` or more done at the start. -/
def run (pre : Name → Nat) (tp : Name → Name) (P : Std.HashMap Name (List Name)) (e : Name)
    (order : List Name) (n : Nat) : Semis :=
  order.foldl (visit pre tp P e) ⟨∅, ∅, ∅, n⟩

variable {g : Graph} {e : Name} {pre : Name → Nat} {R : Name → Prop}
  {tup : Std.HashMap Name Name}

/-- What holds at every step, for the search's tree `tup`. The maps hold
only done blocks. Every block's semidominator so far reaches it along a
path whose blocks after it are numbered at least as high. A done block's
forest parent and label are ancestors of it in the search's tree, and its
label is done. -/
structure Ok (g : Graph) (e : Name) (pre : Name → Nat) (R : Name → Prop)
    (tup : Std.HashMap Name Name) (s : Semis) : Prop where
  lo_pos : 0 < s.lo
  sd_lo : ∀ x, s.sd.contains x = true → s.lo ≤ pre x
  links_lo : ∀ x, s.links.contains x = true → s.lo ≤ pre x
  lab_lo : ∀ x, s.lab.contains x = true → s.lo ≤ pre x
  semi : ∀ x, R x → R (s.semi pre (parentIn tup) x) ∧
    Above g pre (pre x - 1) (s.semi pre (parentIn tup) x) x
  forest : ∀ x, R x → s.lo ≤ pre x →
    Ancestor (parentIn tup) e (s.up (parentIn tup) x) x ∧ s.lo ≤ pre (s.label x) ∧
      Ancestor (parentIn tup) e (s.label x) x

theorem ne_of_lo (hT : Lifted g e pre R tup) {lo : Nat} (hlo : 0 < lo) {x : Name}
    (hx : lo ≤ pre x) : x ≠ e := by
  rintro rfl
  rw [hT.shaped.root_pre] at hx
  omega

/-- A block other than the entry may take its tree parent for its
semidominator. -/
theorem semi_parent (hT : Lifted g e pre R tup)
    (hE : ∀ x, R x → x ≠ e → x ∈ g.getD (parentIn tup x) []) {x : Name} (hx : R x)
    (hxe : x ≠ e) : R (parentIn tup x) ∧ Above g pre (pre x - 1) (parentIn tup x) x := by
  have hp := hT.shaped.up x hx hxe
  have := hp.2
  exact ⟨hp.1, .step .refl (hE x hx hxe) (by omega)⟩

theorem semi_default (hT : Lifted g e pre R tup)
    (hE : ∀ x, R x → x ≠ e → x ∈ g.getD (parentIn tup x) []) {lo : Nat} (hlo : 0 < lo) {x : Name}
    (hx : R x) : R (if lo ≤ pre x then parentIn tup x else x) ∧
      Above g pre (pre x - 1) (if lo ≤ pre x then parentIn tup x else x) x := by
  split
  · exact semi_parent hT hE hx (ne_of_lo hT hlo ‹_›)
  · exact ⟨hx, .refl⟩

theorem not_contains {m : Std.HashMap Name Name} {lo : Nat} {x : Name}
    (h : ∀ y, m.contains y = true → lo ≤ pre y) (hx : ¬ lo ≤ pre x) : m.contains x = false := by
  cases hc : m.contains x
  · rfl
  · exact absurd (h x hc) hx

theorem relabel_self {P : Name → Prop} {lab : Std.HashMap Name Name} {x la : Name} (b : Bool)
    (h1 : P la) (h2 : P (lab.getD x x)) : P ((relabel lab x la b).getD x x) := by
  cases b
  · exact h2
  · simp only [relabel, Std.HashMap.getD_insert_self]; exact h1

theorem relabel_getD {lab : Std.HashMap Name Name} {x la y : Name} {b : Bool} (h : x ≠ y) :
    (relabel lab x la b).getD y y = lab.getD y y := by
  cases b
  · rfl
  · simp [relabel, Std.HashMap.getD_insert, h]

theorem relabel_contains {lab : Std.HashMap Name Name} {x la y : Name} {b : Bool}
    (h : (relabel lab x la b).contains y = true) : x = y ∨ lab.contains y = true := by
  cases b
  · exact .inr h
  · simpa [relabel] using h

theorem squash_lo (tp : Name → Name) (s : Semis) (x : Name) : (squash pre tp s x).lo = s.lo := by
  obtain ⟨sd, links, lab, lo⟩ := s
  simp only [squash]
  split <;> rfl

theorem squash_ok (hT : Lifted g e pre R tup) {s : Semis} (h : s.Ok g e pre R tup) (x : Name) :
    (squash pre (parentIn tup) s x).Ok g e pre R tup := by
  obtain ⟨sd, links, lab, lo⟩ := s
  simp only [squash]
  split
  · rename_i hc
    obtain ⟨hxl, hal⟩ := hc
    refine ⟨h.lo_pos, h.sd_lo, ?_, ?_, h.semi, ?_⟩
    · intro y hy
      rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at hy
      rcases hy with rfl | hy
      · exact hxl
      · exact h.links_lo y hy
    · intro y hy
      dsimp only at hy
      rcases relabel_contains hy with rfl | hy
      · exact hxl
      · exact h.lab_lo y hy
    · intro y hy hly
      by_cases hxy : x = y
      · subst hxy
        obtain ⟨f1, f2, f3⟩ := h.forest x hy hly
        have haR := f1.mem hT.shaped hy
        obtain ⟨a1, a2, a3⟩ := h.forest _ haR hal
        simp only [up, label] at f1 f2 f3 a1 a2 a3 ⊢
        rw [Std.HashMap.getD_insert_self]
        exact ⟨a1.trans f1, relabel_self (P := fun n => lo ≤ pre n ∧ Ancestor (parentIn tup) e n x)
          _ ⟨a2, a3.trans f1⟩ ⟨f2, f3⟩⟩
      · have hf := h.forest y hy hly
        simp only [up, label] at hf ⊢
        rw [Std.HashMap.getD_insert, ite_eq_right (by simpa using hxy), relabel_getD hxy]
        exact hf
  · exact h

theorem foldl_squash_ok (hT : Lifted g e pre R tup) (L : List Name) {s : Semis}
    (h : s.Ok g e pre R tup) :
    (L.foldl (squash pre (parentIn tup)) s).Ok g e pre R tup ∧
      (L.foldl (squash pre (parentIn tup)) s).lo = s.lo := by
  induction L generalizing s with
  | nil => exact ⟨h, rfl⟩
  | cons x L ih =>
    obtain ⟨h1, h2⟩ := ih (squash_ok hT h x)
    exact ⟨h1, h2.trans (squash_lo _ _ _)⟩

theorem eval_spec (hT : Lifted g e pre R tup) {s : Semis} (h : s.Ok g e pre R tup) {u : Name}
    (hu : R u) :
    (eval pre (parentIn tup) s u).1.Ok g e pre R tup ∧ (eval pre (parentIn tup) s u).1.lo = s.lo ∧
      Ancestor (parentIn tup) e (eval pre (parentIn tup) s u).2 u ∧
      ((eval pre (parentIn tup) s u).2 = u ∨ s.lo ≤ pre (eval pre (parentIn tup) s u).2) := by
  simp only [eval]
  split
  · rename_i hul
    obtain ⟨h1, h2⟩ := foldl_squash_ok hT (chain pre (parentIn tup) s u []) h
    obtain ⟨_, f2, f3⟩ := h1.forest u hu (by rw [h2]; exact hul)
    exact ⟨h1, h2, f3, .inr (by rw [← h2]; exact f2)⟩
  · exact ⟨h, rfl, .refl, .inl rfl⟩

/-- Every candidate that the predecessors of `v` offer reaches `v` along a
path whose blocks after it are numbered at least as high as `v`. -/
theorem offer_spec (hT : Lifted g e pre R tup) {v : Name} (hv1 : 0 < pre v) (L : List Name)
    (hL : ∀ u ∈ L, R u ∧ v ∈ g.getD u []) {s : Semis} {best : Name} (h : s.Ok g e pre R tup)
    (hlo : pre v < s.lo) (hb : R best ∧ Above g pre (pre v - 1) best v) :
    (L.foldl (offer pre (parentIn tup)) (s, best)).1.Ok g e pre R tup ∧
      pre v < (L.foldl (offer pre (parentIn tup)) (s, best)).1.lo ∧
      R (L.foldl (offer pre (parentIn tup)) (s, best)).2 ∧
      Above g pre (pre v - 1) (L.foldl (offer pre (parentIn tup)) (s, best)).2 v := by
  induction L generalizing s best with
  | nil => exact ⟨h, hlo, hb⟩
  | cons u L ih =>
    obtain ⟨huR, huv⟩ := hL u (List.mem_cons_self ..)
    obtain ⟨e1, e2, e3, e4⟩ := eval_spec hT h huR
    simp only [List.foldl_cons, offer]
    generalize eval pre (parentIn tup) s u = r at e1 e2 e3 e4 ⊢
    obtain ⟨s', w⟩ := r
    dsimp only at e1 e2 e3 e4 ⊢
    have hwR : R w := e3.mem hT.shaped huR
    have hc : R (s'.semi pre (parentIn tup) w) ∧
        Above g pre (pre v - 1) (s'.semi pre (parentIn tup) w) v := by
      obtain ⟨c1, c2⟩ := e1.semi w hwR
      by_cases hw : s.lo ≤ pre w
      · refine ⟨c1, ((c2.mono (by omega)).trans
          ((hT.ancestor_above e3 huR).mono (by omega))).trans (.step .refl huv (by omega))⟩
      · rcases e4 with rfl | hw'
        · have hnc := not_contains e1.sd_lo (by rw [e2]; exact hw)
          have : s'.semi pre (parentIn tup) w = w := by
            simp only [semi, Std.HashMap.getD_eq_fallback_of_contains_eq_false hnc, e2, ite_eq_right hw]
          rw [this]
          exact ⟨hwR, .step .refl huv (by omega)⟩
        · exact absurd hw' hw
    apply ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) e1 (by rw [e2]; exact hlo)
    split
    · exact hc
    · exact hb

theorem visit_ok (hT : Lifted g e pre R tup)
    (hE : ∀ x, R x → x ≠ e → x ∈ g.getD (parentIn tup x) []) {P : Std.HashMap Name (List Name)}
    (hP : ∀ u y, u ∈ P.getD y [] → R u ∧ y ∈ g.getD u []) {s : Semis} (h : s.Ok g e pre R tup)
    {v : Name} (hv : R v) : (visit pre (parentIn tup) P e s v).Ok g e pre R tup := by
  simp only [visit]
  split
  · rename_i hc
    obtain ⟨hvne, hlo⟩ := hc
    have hv1 : 0 < pre v := hT.shaped.pre_pos hv hvne
    obtain ⟨o1, o2, o3, o4⟩ := offer_spec hT hv1 (P.getD v []) (fun u hu => hP u v hu) h hlo
      (semi_parent hT hE hv hvne)
    generalize (P.getD v []).foldl (offer pre (parentIn tup)) (s, parentIn tup v) = r
      at o1 o2 o3 o4 ⊢
    obtain ⟨⟨sd, links, lab, lo⟩, best⟩ := r
    dsimp only at o1 o2 o3 o4 ⊢
    have hsd : ∀ x, x ≠ v → ∀ d,
        (if pre best < pre (parentIn tup v) then sd.insert v best else sd).getD x d =
          sd.getD x d := by
      intro x hxv d
      split
      · rw [Std.HashMap.getD_insert, ite_eq_right (by simpa using Ne.symm hxv)]
      · rfl
    refine ⟨hv1, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      split at hx
      · rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
        rcases hx with rfl | hx
        · exact Nat.le_refl _
        · exact Nat.le_of_lt (Nat.lt_of_lt_of_le o2 (o1.sd_lo x hx))
      · exact Nat.le_of_lt (Nat.lt_of_lt_of_le o2 (o1.sd_lo x hx))
    · exact fun x hx => Nat.le_of_lt (Nat.lt_of_lt_of_le o2 (o1.links_lo x hx))
    · exact fun x hx => Nat.le_of_lt (Nat.lt_of_lt_of_le o2 (o1.lab_lo x hx))
    · intro x hx
      simp only [semi]
      by_cases hxv : x = v
      · subst hxv
        split
        · rw [Std.HashMap.getD_insert_self]
          exact ⟨o3, o4⟩
        · rw [Std.HashMap.getD_eq_fallback_of_contains_eq_false
            (not_contains o1.sd_lo (Nat.not_le.mpr o2)), ite_eq_left (Nat.le_refl _)]
          exact semi_parent hT hE hx hvne
      · rw [hsd x hxv]
        by_cases hxl : lo ≤ pre x
        · rw [ite_eq_left (Nat.le_trans (Nat.le_of_lt o2) hxl)]
          have := o1.semi x hx
          simp only [semi, ite_eq_left hxl] at this
          exact this
        · rw [Std.HashMap.getD_eq_fallback_of_contains_eq_false (not_contains o1.sd_lo hxl)]
          exact semi_default hT hE hv1 hx
    · intro x hx hxl
      simp only [up, label]
      by_cases hx1 : lo ≤ pre x
      · obtain ⟨f1, f2, f3⟩ := o1.forest x hx hx1
        exact ⟨f1, Nat.le_trans (Nat.le_of_lt o2) f2, f3⟩
      · rw [Std.HashMap.getD_eq_fallback_of_contains_eq_false (not_contains o1.links_lo hx1),
          Std.HashMap.getD_eq_fallback_of_contains_eq_false (not_contains o1.lab_lo hx1)]
        exact ⟨.up (ne_of_lo hT hv1 hxl) .refl, hxl, .refl⟩
  · exact h

/-- What the computation ends with: every block's semidominator reaches it
along a path whose blocks after it are numbered at least as high. -/
theorem run_spec (hT : Lifted g e pre R tup)
    (hE : ∀ x, R x → x ≠ e → x ∈ g.getD (parentIn tup x) []) {P : Std.HashMap Name (List Name)}
    (hP : ∀ u y, u ∈ P.getD y [] → R u ∧ y ∈ g.getD u []) (order : List Name)
    (hord : ∀ x ∈ order, R x) {n : Nat} (hn : 0 < n) :
    ∀ x, R x → R ((run pre (parentIn tup) P e order n).semi pre (parentIn tup) x) ∧
      Above g pre (pre x - 1) ((run pre (parentIn tup) P e order n).semi pre (parentIn tup) x) x := by
  have h0 : (⟨∅, ∅, ∅, n⟩ : Semis).Ok g e pre R tup := by
    refine ⟨hn, fun x hx => by simp at hx, fun x hx => by simp at hx, fun x hx => by simp at hx,
      fun x hx => ?_, fun x hx hxl => ?_⟩
    · simp only [semi, Std.HashMap.getD_empty]
      exact semi_default hT hE hn hx
    · simp only [up, label, Std.HashMap.getD_empty]
      exact ⟨.up (ne_of_lo hT hn hxl) .refl, hxl, .refl⟩
  suffices ∀ (L : List Name) (s : Semis), (∀ x ∈ L, R x) → s.Ok g e pre R tup →
      (L.foldl (visit pre (parentIn tup) P e) s).Ok g e pre R tup from
    (this order _ hord h0).semi
  intro L
  induction L with
  | nil => exact fun _ _ h => h
  | cons v L ih =>
    exact fun s hL h => ih _ (fun x hx => hL x (List.mem_cons_of_mem _ hx))
      (visit_ok hT hE hP h (hL v (List.mem_cons_self ..)))

end Semis

end FirRef.Dom
