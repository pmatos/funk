import Fir.Validation.Tables

/-!
Reachability and dominance are about paths in a function's graph, and a path
can be of any length, so the check finds them with a search. `search` keeps
the nodes it has seen and a list of nodes still to visit. It visits a node
at most once, so it ends, and it finds exactly the nodes that some path
reaches (`contains_search_iff`). Validation asks two kinds of question of
it: which blocks the entry reaches, and which it reaches without passing
through a given block.

The graph is a table from each node to the nodes it has edges to. A node
that is not a key of the table has no edges.
-/

namespace Fir

variable {α : Type}

theorem length_filter_lt {l : List α} {p q : α → Bool} {x : α} (h : ∀ y, q y = true → p y = true)
    (hx : x ∈ l) (hp : p x = true) (hq : q x = false) :
    (l.filter q).length < (l.filter p).length := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    have hle : (l.filter q).length ≤ (l.filter p).length := by
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      exact List.countP_mono_left fun y _ => h y
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [hp, hq]; omega
    · have := ih hx
      by_cases hqa : q a = true
      · simp [hqa, h a hqa]; omega
      · by_cases hpa : p a = true <;> simp [hqa, hpa] <;> omega

variable [BEq α] [Hashable α]

/--
`Reach next ok start y`: some path reaches `y` from a node of `start`,
following the edges `next` and entering only nodes for which `ok` holds,
the first one included.
-/
inductive Reach (next : α → List α) (ok : α → Bool) (start : List α) : α → Prop
  | start {x : α} : x ∈ start → ok x = true → Reach next ok start x
  | step {x y : α} : Reach next ok start x → y ∈ next x → ok y = true → Reach next ok start y

/-- The nodes of the graph `g` that `seen` does not hold. -/
def unseen (g : Std.HashMap α (List α)) (seen : Std.HashSet α) : Nat :=
  (g.keys.filter fun y => !seen.contains y).length

variable [LawfulBEq α]

theorem unseen_insert_lt {g : Std.HashMap α (List α)} {seen : Std.HashSet α} {x : α}
    (hg : g.contains x = true) (hs : seen.contains x = false) :
    unseen g (seen.insert x) < unseen g seen := by
  apply length_filter_lt (x := x)
  · intro y hy
    simp only [Std.HashSet.contains_insert, Bool.not_or, Bool.and_eq_true] at hy
    exact hy.2
  · exact Std.HashMap.mem_keys.mpr (Std.HashMap.mem_iff_contains.mpr hg)
  · simp [hs]
  · simp

/--
The search. It visits the nodes of `work` in turn. A node that is a key of
the graph, that `ok` admits and that it has not seen, it adds to `seen`, and
it puts the node's successors in front of the rest of the work. The result
is every node it has seen.
-/
def search [LawfulBEq α] (g : Std.HashMap α (List α)) (ok : α → Bool) (seen : Std.HashSet α) :
    List α → Std.HashSet α
  | [] => seen
  | x :: work =>
    if _h : g.contains x && ok x && !seen.contains x then
      search g ok (seen.insert x) (g.getD x [] ++ work)
    else search g ok seen work
termination_by work => (unseen g seen, work.length)
decreasing_by
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at _h
    exact Prod.Lex.left _ _ (unseen_insert_lt _h.1.1 _h.2)
  · exact Prod.Lex.right _ (by simp)

variable {g : Std.HashMap α (List α)} {ok : α → Bool}

/-- The search keeps what it has seen. -/
theorem search_mono {seen : Std.HashSet α} {work : List α} {z : α} (hz : z ∈ seen) :
    z ∈ search g ok seen work := by
  fun_induction search g ok seen work with
  | case1 => exact hz
  | case2 seen x work h ih => exact ih (Std.HashSet.mem_insert.mpr (Or.inr hz))
  | case3 seen x work h ih => exact ih hz

/-- The search sees every node of its work that is a key of the graph and
that `ok` admits. -/
theorem search_covers {seen : Std.HashSet α} {work : List α} {z : α} (hz : z ∈ work)
    (hg : g.contains z = true) (hok : ok z = true) : z ∈ search g ok seen work := by
  fun_induction search g ok seen work with
  | case1 => simp at hz
  | case2 seen x work h ih =>
    rcases List.mem_cons.mp hz with rfl | hz
    · exact search_mono (Std.HashSet.mem_insert.mpr (Or.inl (beq_self_eq_true _)))
    · exact ih (List.mem_append_right _ hz)
  | case3 seen x work h ih =>
    rcases List.mem_cons.mp hz with rfl | hz
    · simp only [hg, hok, Bool.true_and, Bool.not_eq_true', Bool.not_eq_false] at h
      exact search_mono (Std.HashSet.mem_iff_contains.mpr (by simpa using h))
    · exact ih hz

/-- What the search ends with is closed under the edges into the nodes that
it may visit, when each node already seen has its successors in it. -/
theorem search_closed {seen : Std.HashSet α} {work : List α}
    (hseen : ∀ x ∈ seen, ∀ y ∈ g.getD x [], g.contains y = true → ok y = true →
      y ∈ search g ok seen work) :
    ∀ x ∈ search g ok seen work, ∀ y ∈ g.getD x [], g.contains y = true → ok y = true →
      y ∈ search g ok seen work := by
  fun_induction search g ok seen work with
  | case1 => exact hseen
  | case2 seen x work h ih =>
    apply ih
    intro x' hx' y hy hg hok
    rcases Std.HashSet.mem_insert.mp hx' with hx | hx
    · rw [beq_iff_eq] at hx
      subst hx
      exact search_covers (List.mem_append_left _ hy) hg hok
    · exact hseen x' hx y hy hg hok
  | case3 seen x work h ih =>
    apply ih
    intro x' hx' y hy hg hok
    exact hseen x' hx' y hy hg hok

/-- Every node that the search sees is reached, when every node of `seen`
is, and every node of the work that `ok` admits. -/
theorem search_sound {seen : Std.HashSet α} {work : List α} {st : List α}
    (hseen : ∀ x ∈ seen, Reach (g.getD · []) ok st x)
    (hwork : ∀ x ∈ work, ok x = true → Reach (g.getD · []) ok st x) :
    ∀ y ∈ search g ok seen work, Reach (g.getD · []) ok st y := by
  fun_induction search g ok seen work with
  | case1 => exact hseen
  | case2 seen x work h ih =>
    simp only [Bool.and_eq_true] at h
    have hx := hwork x (List.mem_cons_self ..) h.1.2
    apply ih
    · intro z hz
      rcases Std.HashSet.mem_insert.mp hz with e | hz
      · rw [beq_iff_eq] at e; exact e ▸ hx
      · exact hseen z hz
    · intro z hz hok
      rcases List.mem_append.mp hz with hz | hz
      · exact .step hx hz hok
      · exact hwork z (List.mem_cons_of_mem _ hz) hok
  | case3 seen x work h ih =>
    exact ih hseen fun z hz => hwork z (List.mem_cons_of_mem _ hz)

/-- The search from `start`, with nothing seen, finds exactly the nodes of
the graph that a path reaches from `start`. -/
theorem contains_search_iff {start : List α} {y : α} (hy : g.contains y = true) :
    y ∈ search g ok ∅ start ↔ Reach (g.getD · []) ok start y := by
  constructor
  · exact search_sound (by simp) (fun x hx hok => .start hx hok) y
  · intro h
    suffices ∀ z, Reach (g.getD · []) ok start z → g.contains z = true → z ∈ search g ok ∅ start from
      this y h hy
    intro z hz
    induction hz with
    | start hx hok => exact fun hg => search_covers hx hg hok
    | @step x z _ hz hok ih =>
      intro hg
      have hgx : g.contains x = true := by
        apply Classical.byContradiction
        intro hn
        rw [Std.HashMap.getD_eq_fallback (by simpa using hn)] at hz
        simp at hz
      exact search_closed (by simp) x (ih hgx) z hz hg hok

end Fir
