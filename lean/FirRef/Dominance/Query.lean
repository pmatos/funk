import FirRef.Dominance.Place

/-!
`fir-ref`'s answer to "does block `a` dominate block `l`": the dominator
tree, built once per function (`Oracle.build`), then one walk up from `l`
per question, in steps logarithmic in the depth of `l` (`climbs`).

The tree is built in four steps: the search's tree (`tree`), the
semidominators (`Semis.run`), the placement of each block under the nearest
ancestor of its parent numbered at most its semidominator (`place`), and
the check that each block's parent is an ancestor of each of its
predecessors (`fixed`). The search's tree has the facts of `Lifted`, and
each step keeps them, so when the check passes the tree's ancestors are
the dominators. If it ever failed, the lifting of `FirRef.Dominance.Lift`
would go on from the placed tree until no block moves, and would end with
the dominator tree too; on every graph that the tests try, the check
passes. `dominance_eq` proves the answers equal to the spec's search,
`dominatesIn`, for every pair of labels.
-/

namespace FirRef.Dom

open Fir

variable {g : Graph} {e : Name}

/-! # The search's tree -/

/-- The search's tree has the facts that the lifting keeps. -/
theorem tree_lifted (he : g.contains e = true) :
    Lifted g e (tree g e).num (fun x => (tree g e).pre.contains x = true) (tree g e).up := by
  have h := tree_inv he
  have hs : Shaped (parentIn (tree g e).up) (tree g e).num
      (fun x => (tree g e).pre.contains x = true) e :=
    ⟨h.root, h.root_num, fun y hy hye => ⟨(h.parent y hy hye).1, (h.parent y hy hye).2.1⟩⟩
  refine ⟨hs, fun y hy hye => .step .refl (h.parent y hy hye).2.2 (h.parent y hy hye).2.1, ?_⟩
  intro c hc z hzc hn
  exact avoid c hc z hzc hn
where
  avoid (c : Name) (hc : (tree g e).pre.contains c = true) (z : Name) (hzc : z ≠ c)
      (hn : ¬ Ancestor (parentIn (tree g e).up) e z c) : Avoids g e z c := by
    have h := tree_inv he
    by_cases hce : c = e
    · subst hce
      exact .start (List.mem_singleton_self _) (bne_iff_ne.mpr (Ne.symm hzc))
    · obtain ⟨hp, hlt, hedge⟩ := h.parent c hc hce
      have hzp : z ≠ (tree g e).parent c := fun h' => hn (h' ▸ .up hce .refl)
      have hnp : ¬ Ancestor (parentIn (tree g e).up) e z ((tree g e).parent c) :=
        fun h' => hn (.up hce h')
      exact .step (avoid _ hp z hzp hnp) hedge (bne_iff_ne.mpr (Ne.symm hzc))
  termination_by (tree g e).num c
  decreasing_by exact hlt

/-- The setting of the lifting for the search's tree. -/
theorem tree_setting (he : g.contains e = true) :
    Setting g e (tree g e).num (fun x => (tree g e).pre.contains x = true)
      (preds g (tree g e).order.reverse) (tree g e).order.reverse := by
  have h := tree_inv he
  refine ⟨h.root, h.root_num, fun u y => ?_, fun x => ?_, fun _ y hr hy => tree_complete he hr hy,
    h.key⟩
  · rw [mem_preds, List.mem_reverse, h.order]
  · rw [List.mem_reverse, h.order]

/-! # The answer to every question of dominance -/

/-- The dominator tree of a function's graph, with what its walk reads: each
reached block's number, its parent and its jump pointer. -/
structure Oracle where
  pre : Std.HashMap Name Nat
  par : Std.HashMap Name Name
  jump : Std.HashMap Name Name

/-- Whether block `a` dominates block `l`: they are one block, the entry
does not reach `l`, or `a` is an ancestor of `l` in the dominator tree. -/
def Oracle.dominates (o : Oracle) (a l : Name) : Bool :=
  a == l || !o.pre.contains l || climbs (o.pre.getD · 0) (parentIn o.par) (parentIn o.jump) a l

/-- The search's tree `t` of a function's graph, with the predecessors `P`
and the blocks `order` it numbers, in increasing order, placed by their
semidominators. -/
def Found.placing (t : Found) (P : Std.HashMap Name (List Name)) (e : Name)
    (order : List Name) : Placing :=
  let s := Semis.run t.num (parentIn t.up) P e t.order t.count
  place t.num (Semis.semi t.num (parentIn t.up) s) e order t.up

/-- The dominator tree of the graph `g` from the entry `e`. -/
def Oracle.build (g : Graph) (e : Name) : Oracle :=
  let t := tree g e
  let order := t.order.reverse
  let P := preds g order
  let st := t.placing P e order
  if fixed t.num P e st.pm st.js.jump order then ⟨t.pre, st.pm, st.js.jump⟩
  else
    let pm := lifts t.num P e order st.pm
    ⟨t.pre, pm, (jumps pm e order).jump⟩

/-- What the build ends with: a tree with the facts of `Lifted`, in which
each block's parent is an ancestor of each of its predecessors, and jump
pointers that are ancestors. -/
theorem build_spec (he : g.contains e = true) :
    ∃ pm jump, Oracle.build g e = ⟨(tree g e).pre, pm, jump⟩ ∧
      Lifted g e (tree g e).num (fun x => (tree g e).pre.contains x = true) pm ∧
      (∀ b, (tree g e).pre.contains b = true → b ≠ e →
        ∀ u ∈ (preds g (tree g e).order.reverse).getD b [],
          Ancestor (parentIn pm) e (parentIn pm b) u) ∧
      ∀ x, (tree g e).pre.contains x = true →
        Ancestor (parentIn pm) e (parentIn jump x) x ∧
          (tree g e).pre.contains (parentIn jump x) = true := by
  have S := tree_setting he
  have hi := tree_inv he
  have hsem := Semis.run_spec (tree_lifted he) (fun x hx hxe => (hi.parent x hx hxe).2.2)
    (fun u y hu => (S.preds u y).mp hu)
    (tree g e).order (fun x hx => (hi.order x).mp hx)
    (Nat.lt_of_le_of_lt (Nat.zero_le _) (hi.lt e hi.root))
  have hpl : ((tree g e).placing (preds g (tree g e).order.reverse) e
      (tree g e).order.reverse).Ok g e (tree g e).num (fun x => (tree g e).pre.contains x = true) :=
    place_ok hsem (tree_lifted he) (tree g e).order.reverse (fun x hx => (S.order x).mp hx)
  simp only [Oracle.build]
  generalize (tree g e).placing (preds g (tree g e).order.reverse) e (tree g e).order.reverse = st
    at hpl ⊢
  cases hf : fixed (tree g e).num (preds g (tree g e).order.reverse) e st.pm st.js.jump
    (tree g e).order.reverse
  · rw [ite_eq_right Bool.false_ne_true]
    obtain ⟨h, hfix⟩ := lifts_spec S hpl.lifted
    exact ⟨_, _, rfl, h, hfix, jumps_ancestor rfl h.shaped _ (fun x hx => (S.order x).mp hx)⟩
  · rw [ite_eq_left rfl]
    exact ⟨_, _, rfl, hpl.lifted, fixed_spec S hpl.lifted.shaped hpl.jump hf, hpl.jump⟩

/-- The dominator tree of the graph `g` whose paths start at the entry `e?`,
when the entry is a block of the graph. It is data, not a function, so that
a caller builds it once and asks it many questions. -/
def dominance (g : Graph) (e? : Option Name) : Option Oracle :=
  match e? with
  | some e => if g.contains e then some (Oracle.build g e) else none
  | none => none

/-- Whether block `a` dominates block `l`, by the tree `o`. With no tree, no
path starts, so every block dominates every block. -/
def dominatesBy : Option Oracle → Name → Name → Bool
  | some o, a, l => o.dominates a l
  | none, _, _ => true

/-- The spec's search finds only the blocks of the graph, beside those it
has seen. -/
theorem search_key {ok : Name → Bool} {seen : Std.HashSet Name} {work : List Name} {z : Name}
    (hz : z ∈ search g ok seen work) : z ∈ seen ∨ g.contains z = true := by
  fun_induction search g ok seen work with
  | case1 => exact .inl hz
  | case2 seen x work h ih =>
    rcases ih hz with hz | hz
    · rcases Std.HashSet.mem_insert.mp hz with hx | hz
      · rw [beq_iff_eq] at hx
        subst hx
        simp only [Bool.and_eq_true] at h
        exact .inr h.1.1
      · exact .inl hz
    · exact .inr hz
  | case3 seen x work h ih => exact ih hz

theorem dominatesIn_nil (g : Graph) (a l : Name) : dominatesIn g [] a l = true := by
  simp [dominatesIn, avoidingIn, search]

theorem dominatesIn_absent {e : Name} (he : g.contains e = false) (a l : Name) :
    dominatesIn g [e] a l = true := by
  simp [dominatesIn, avoidingIn, search, he]

/-- `fir-ref`'s dominance is the spec's, for every pair of labels. -/
theorem dominance_eq (g : Graph) (e? : Option Name) :
    dominatesBy (dominance g e?) = dominatesIn g e?.toList := by
  funext a l
  cases e? with
  | none => exact (dominatesIn_nil g a l).symm
  | some e =>
    unfold dominance
    simp only [Option.toList_some]
    split
    · rename_i he
      have S := tree_setting he
      obtain ⟨pm, jump, hb, h, hfix, hj⟩ := build_spec he
      simp only [dominatesBy, Oracle.dominates, hb, dominatesIn, avoidingIn]
      by_cases hal : a = l
      · subst hal; simp
      · have hal' : (a == l) = false := beq_eq_false_iff_ne.mpr hal
        rw [hal', Bool.false_or, Bool.false_or]
        by_cases hl : (tree g e).pre.contains l = true
        · rw [hl, Bool.not_true, Bool.false_or,
            show (fun x => (tree g e).pre.getD x 0) = (tree g e).num from rfl]
          have hgl := S.key l hl
          rw [Bool.eq_iff_iff, climbs_iff h.shaped hj hl, Bool.not_eq_true', ← Bool.not_eq_true,
            ← Std.HashSet.mem_iff_contains, contains_search_iff hgl, h.ancestor_iff S hfix hl]
          simp [hal]
        · rw [Bool.not_eq_true] at hl
          rw [hl, Bool.not_false, Bool.true_or, eq_comm, Bool.not_eq_true', ← Bool.not_eq_true,
            ← Std.HashSet.mem_iff_contains]
          intro hm
          rcases search_key hm with hm' | hgl
          · simp at hm'
          · have := S.complete _ l ((contains_search_iff hgl).mp hm) hgl
            rw [hl] at this
            exact Bool.false_ne_true this
    · rename_i he
      exact (dominatesIn_absent (Bool.eq_false_iff.mpr he) a l).symm

end FirRef.Dom
