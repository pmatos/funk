import FirRef.Dominance.Lift

/-!
`fir-ref`'s answer to "does block `a` dominate block `l`": the search's
tree, lifted into the dominator tree once per function (`Oracle.build`),
then one walk up from `l` per question. The walk follows jump pointers, so
it takes a number of steps logarithmic in the depth of `l`. A block's jump
pointer is an ancestor of the block, chosen by the rule of Myers' skew-binary
lists (E. W. Myers, "An applicative random-access stack", 1983); the proofs
need only that it is an ancestor. `dominance_eq` proves the answers equal to
the spec's search, `dominatesIn`, for every pair of labels.
-/

namespace FirRef

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
    apply ih _ (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    intro x hx
    have hy := hL y (List.mem_cons_self ..)
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

/-! # The walk -/

/-- Whether `a` is an ancestor of `cur`: walk up from `cur`, by jump
pointers that do not pass `a`'s number and otherwise by parents, until the
number is at most `a`'s. The checks on the numbers make the walk end on any
input; on a shaped tree they always pass. -/
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

/-- The dominator tree of the graph `g` from the entry `e`. -/
def Oracle.build (g : Graph) (e : Name) : Oracle :=
  let t := tree g e
  let order := t.order.reverse
  let pm := lifts t.num (preds g order) e order t.up
  ⟨t.pre, pm, (jumps pm e order).jump⟩

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
      obtain ⟨h, hfix⟩ := lifts_spec S (tree_lifted he)
      have hj := jumps_ancestor rfl h.shaped _ (fun x hx => (S.order x).mp hx)
      simp only [dominatesBy, Oracle.dominates, Oracle.build, dominatesIn, avoidingIn]
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

end FirRef
