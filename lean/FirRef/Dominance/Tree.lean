import Fir.Validation.Graph

/-!
The first step of `fir-ref`'s dominator tree: a depth-first search of a
function's graph from its entry, which numbers each block it reaches in the
order it reaches it and records the block it came from. Those records form
a spanning tree of the reached blocks whose edges are edges of the graph,
and each block's number is above its parent's. The search numbers every
block of the graph that a path from the entry reaches (`tree_complete`),
and only blocks of the graph (`tree_key`).

Like the spec's `search`, it keeps what is left to visit on a list and makes
only tail calls, so it takes no stack per block.
-/

namespace FirRef.Dom

open Fir

/-- A function's graph, as the spec's check builds it (`Func.graph`). -/
abbrev Graph := Std.HashMap Name (List Name)

/-- What the search has found: the number of each block it reached, the
block it reached each one from, the blocks it reached, last first, and how
many. -/
structure Found where
  pre : Std.HashMap Name Nat
  up : Std.HashMap Name Name
  order : List Name
  count : Nat

/-- The blocks of the graph `g` that `pre` does not number. -/
def unnumbered (g : Graph) (pre : Std.HashMap Name Nat) : Nat :=
  (g.keys.filter fun y => !pre.contains y).length

theorem unnumbered_insert_lt {g : Graph} {pre : Std.HashMap Name Nat} {x : Name} {n : Nat}
    (hg : g.contains x = true) (hs : pre.contains x = false) :
    unnumbered g (pre.insert x n) < unnumbered g pre := by
  apply length_filter_lt (x := x)
  · intro y hy
    simp only [Std.HashMap.contains_insert, Bool.not_or, Bool.and_eq_true] at hy
    exact hy.2
  · exact Std.HashMap.mem_keys.mpr (Std.HashMap.mem_iff_contains.mpr hg)
  · simp [hs]
  · simp

/-- The search. Each item of the work is a block and the block it was
reached from. A block of the graph that is not yet numbered gets the next
number and that parent, and its successors go in front of the rest of the
work. -/
def dfs (g : Graph) (s : Found) : List (Name × Name) → Found
  | [] => s
  | (x, p) :: work =>
    if _h : g.contains x && !s.pre.contains x then
      dfs g ⟨s.pre.insert x s.count, s.up.insert x p, x :: s.order, s.count + 1⟩
        ((g.getD x []).map (·, x) ++ work)
    else dfs g s work
termination_by work => (unnumbered g s.pre, work.length)
decreasing_by
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at _h
    exact Prod.Lex.left _ _ (unnumbered_insert_lt _h.1 _h.2)
  · exact Prod.Lex.right _ (by simp)

/-- The search from the entry `e`, which it numbers 0. -/
def tree (g : Graph) (e : Name) : Found :=
  dfs g ⟨(∅ : Std.HashMap Name Nat).insert e 0, ∅, [e], 1⟩ ((g.getD e []).map (·, e))

/-- The parent of a reached block other than the entry. -/
def Found.parent (s : Found) (x : Name) : Name := s.up.getD x x

/-- The number of a reached block. -/
def Found.num (s : Found) (x : Name) : Nat := s.pre.getD x 0

/-- What holds of the search from the entry `e` at every step. -/
structure Found.Inv (g : Graph) (e : Name) (s : Found) : Prop where
  key : ∀ x, s.pre.contains x = true → g.contains x = true
  root : s.pre.contains e = true
  root_num : s.num e = 0
  parent : ∀ x, s.pre.contains x = true → x ≠ e →
    s.pre.contains (s.parent x) = true ∧ s.num (s.parent x) < s.num x ∧
      x ∈ g.getD (s.parent x) []
  lt : ∀ x, s.pre.contains x = true → s.num x < s.count
  order : ∀ x, x ∈ s.order ↔ s.pre.contains x = true

/-- Each item of the work comes from a reached block, along an edge. -/
def Found.WorkOk (g : Graph) (s : Found) (work : List (Name × Name)) : Prop :=
  ∀ w ∈ work, s.pre.contains w.2 = true ∧ w.1 ∈ g.getD w.2 []

variable {g : Graph}

/-- The search after it numbers `x`, reached from `p`. -/
def Found.add (s : Found) (x p : Name) : Found :=
  ⟨s.pre.insert x s.count, s.up.insert x p, x :: s.order, s.count + 1⟩

theorem Found.contains_add (s : Found) (x p y : Name) :
    (s.add x p).pre.contains y = (x == y || s.pre.contains y) := by
  simp [Found.add, Std.HashMap.contains_insert]

theorem Found.num_add (s : Found) (x p y : Name) :
    (s.add x p).num y = if x = y then s.count else s.num y := by
  simp [Found.add, Found.num, Std.HashMap.getD_insert]

theorem Found.parent_add (s : Found) (x p y : Name) :
    (s.add x p).parent y = if x = y then p else s.parent y := by
  simp [Found.add, Found.parent, Std.HashMap.getD_insert]

theorem Found.inv_add {e : Name} {s : Found} {x p : Name} (h : s.Inv g e)
    (hgx : g.contains x = true) (hnx : s.pre.contains x = false)
    (hpc : s.pre.contains p = true) (hpx : x ∈ g.getD p []) : (s.add x p).Inv g e := by
  have hxe : x ≠ e := fun h' => by rw [h'] at hnx; simp [h.root] at hnx
  have hne : ∀ y, s.pre.contains y = true → x ≠ y := fun y hy h' => by
    rw [h'] at hnx; simp [hy] at hnx
  constructor
  · intro y hy
    rw [Found.contains_add] at hy
    by_cases hyx : x = y
    · exact hyx ▸ hgx
    · rw [beq_eq_false_iff_ne.mpr hyx, Bool.false_or] at hy
      exact h.key y hy
  · simp [Found.contains_add, h.root]
  · rw [Found.num_add, ite_eq_right hxe]
    exact h.root_num
  · intro y hy hye
    rw [Found.contains_add] at hy
    by_cases hyx : x = y
    · subst hyx
      rw [Found.parent_add, ite_eq_left rfl, Found.contains_add, Found.num_add, Found.num_add,
        ite_eq_right (hne p hpc), ite_eq_left rfl]
      exact ⟨by simp [hpc], h.lt p hpc, hpx⟩
    · rw [beq_eq_false_iff_ne.mpr hyx, Bool.false_or] at hy
      obtain ⟨h1, h2, h3⟩ := h.parent y hy hye
      rw [Found.parent_add, ite_eq_right hyx, Found.contains_add, Found.num_add, Found.num_add,
        ite_eq_right (hne _ h1), ite_eq_right hyx]
      exact ⟨by simp [h1], h2, h3⟩
  · intro y hy
    rw [Found.contains_add] at hy
    show (s.add x p).num y < s.count + 1
    rw [Found.num_add]
    by_cases hyx : x = y
    · rw [ite_eq_left hyx]; exact Nat.lt_succ_self _
    · rw [beq_eq_false_iff_ne.mpr hyx, Bool.false_or] at hy
      rw [ite_eq_right hyx]
      exact Nat.lt_succ_of_lt (h.lt y hy)
  · intro y
    show y ∈ x :: s.order ↔ _
    rw [List.mem_cons, h.order, Found.contains_add, Bool.or_eq_true, beq_iff_eq]
    exact ⟨fun h' => h'.imp Eq.symm id, fun h' => h'.imp Eq.symm id⟩

theorem dfs_inv {e : Name} {s : Found} {work : List (Name × Name)} (h : s.Inv g e)
    (hw : s.WorkOk g work) : (dfs g s work).Inv g e := by
  fun_induction dfs g s work with
  | case1 => exact h
  | case2 s x p work hx ih =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx
    obtain ⟨hpc, hpx⟩ := hw (x, p) (List.mem_cons_self ..)
    apply ih (Found.inv_add h hx.1 hx.2 hpc hpx)
    intro w hw'
    rcases List.mem_append.mp hw' with hw' | hw'
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw'
      exact ⟨by simp [Std.HashMap.contains_insert], hy⟩
    · obtain ⟨h1, h2⟩ := hw w (List.mem_cons_of_mem _ hw')
      exact ⟨by simp [Std.HashMap.contains_insert, h1], h2⟩
  | case3 s x p work _ ih =>
    exact ih h fun w hw' => hw w (List.mem_cons_of_mem _ hw')

/-- The search keeps what it has numbered. -/
theorem dfs_mono {s : Found} {work : List (Name × Name)} {z : Name}
    (hz : s.pre.contains z = true) : (dfs g s work).pre.contains z = true := by
  fun_induction dfs g s work with
  | case1 => exact hz
  | case2 s x p work h ih => exact ih (by simp [Std.HashMap.contains_insert, hz])
  | case3 s x p work h ih => exact ih hz

/-- The search numbers every block of the graph in its work. -/
theorem dfs_covers {s : Found} {work : List (Name × Name)} {z p : Name} (hz : (z, p) ∈ work)
    (hg : g.contains z = true) : (dfs g s work).pre.contains z = true := by
  fun_induction dfs g s work with
  | case1 => simp at hz
  | case2 s x q work h ih =>
    rcases List.mem_cons.mp hz with hz | hz
    · cases hz
      exact dfs_mono (by simp [Std.HashMap.contains_insert])
    · exact ih (List.mem_append_right _ hz)
  | case3 s x q work h ih =>
    rcases List.mem_cons.mp hz with hz | hz
    · cases hz
      simp only [hg, Bool.true_and, Bool.not_eq_true', Bool.not_eq_false] at h
      exact dfs_mono h
    · exact ih hz

/-- What the search ends with holds the successors of each block it numbers,
when each block numbered already has its successors in it. -/
theorem dfs_closed {s : Found} {work : List (Name × Name)}
    (hs : ∀ x, s.pre.contains x = true → ∀ y ∈ g.getD x [], g.contains y = true →
      (dfs g s work).pre.contains y = true) :
    ∀ x, (dfs g s work).pre.contains x = true → ∀ y ∈ g.getD x [], g.contains y = true →
      (dfs g s work).pre.contains y = true := by
  fun_induction dfs g s work with
  | case1 => exact hs
  | case2 s x p work h ih =>
    apply ih
    intro x' hx' y hy hg
    rw [Std.HashMap.contains_insert] at hx'
    rcases Bool.or_eq_true_iff.mp hx' with hx | hx
    · rw [beq_iff_eq] at hx
      subst hx
      exact dfs_covers (List.mem_append_left _ (List.mem_map.mpr ⟨y, hy, rfl⟩)) hg
    · exact hs x' hx y hy hg
  | case3 s x p work h ih => exact ih hs

theorem tree_inv {e : Name} (he : g.contains e = true) : (tree g e).Inv g e := by
  apply dfs_inv
  · constructor
    · intro x hx
      simp only [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false,
        beq_iff_eq] at hx
      exact hx ▸ he
    · simp
    · simp [Found.num]
    · intro x hx hxe
      simp only [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false,
        beq_iff_eq] at hx
      exact absurd hx.symm hxe
    · intro x hx
      simp only [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false,
        beq_iff_eq] at hx
      subst hx; simp [Found.num]
    · intro x
      simp only [List.mem_singleton, Std.HashMap.contains_insert, Std.HashMap.contains_empty,
        Bool.or_false, beq_iff_eq]
      exact ⟨Eq.symm, Eq.symm⟩
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
    exact ⟨by simp, hy⟩

/-- The search reaches every block of the graph that a path from the entry
reaches, whatever blocks the path may enter. -/
theorem tree_complete {e : Name} {ok : Name → Bool} {y : Name} (he : g.contains e = true)
    (hr : Reach (g.getD · []) ok [e] y) (hy : g.contains y = true) :
    (tree g e).pre.contains y = true := by
  have hclosed := dfs_closed (g := g)
    (s := ⟨(∅ : Std.HashMap Name Nat).insert e 0, ∅, [e], 1⟩) (work := (g.getD e []).map (·, e))
    (by
      intro x hx y hy hg
      simp only [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false,
        beq_iff_eq] at hx
      subst hx
      exact dfs_covers (List.mem_map.mpr ⟨y, hy, rfl⟩) hg)
  induction hr with
  | start hx =>
    rw [List.mem_singleton] at hx
    subst hx
    exact dfs_mono (by simp)
  | @step x z _ hz _ ih =>
    have hgx : g.contains x = true := by
      apply Classical.byContradiction
      intro hn
      rw [Std.HashMap.getD_eq_fallback (by simpa using hn)] at hz
      simp at hz
    exact hclosed x (ih hgx) z hz hy

/-- The blocks that the search numbers are blocks of the graph. -/
theorem tree_key {e : Name} {x : Name} (he : g.contains e = true)
    (hx : (tree g e).pre.contains x = true) : g.contains x = true :=
  (tree_inv he).key x hx

end FirRef.Dom
