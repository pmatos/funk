import Fir.Execution.TraceEscape

/-!
# What an external call lets escape is the closure

What an external call lets escape (`TraceState.escapeCall`) is exactly the
closure of its pointer arguments and of the allocations that had escaped:

* _Reachable_: an allocation is reachable from the pointers `qs` in the
  traced state `s` when it had escaped, or is the live allocation of one of
  the pointers, or is the live allocation of a pointer that a unit of a
  reachable allocation holds.
* _Sound_: every allocation that has a handle after the call is reachable.
* _Closed_: every reachable allocation has a handle after the call.

With the prefix law (`TraceState.escapeCall_prefix`), the call keeps each
handle that the world already knew and gives new handles to just the
allocations that the call reaches.
-/

namespace Fir

open Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] (μ : Nat → Mem)

/-- The allocations reachable from the pointers `qs`, each with the number
of its memory, in the traced state `s`, where the memory numbered `n` is
`μ n`: those that had escaped, the live allocation of each of the pointers,
and the live allocation of each pointer that a unit of a reachable
allocation holds. -/
inductive TraceState.Reaches (s : TraceState Mem unit) (qs : List (Nat × Pointer)) :
    Mem × AllocId → Prop
  | escaped {p : Mem × AllocId} : p ∈ s.escaped → TraceState.Reaches s qs p
  | arg {n : Nat} {p : Pointer} {a : AllocId} : (n, p) ∈ qs → p.prov = some a →
      s.Live (μ n) a → TraceState.Reaches s qs (μ n, a)
  | unit {x : Mem} {a : AllocId} {n : Nat} {p : Pointer} {b : AllocId} :
      TraceState.Reaches s qs (x, a) → (n, p) ∈ s.ptrsIn x a → p.prov = some b →
        s.Live (μ n) b → TraceState.Reaches s qs (μ n, b)

variable {μ}

/-- Traced states with the same memories agree on which allocations are
live. -/
theorem TraceState.live_congr {s t : TraceState Mem unit} (h : t.mem = s.mem) (x : Mem)
    (a : AllocId) : t.Live x a ↔ s.Live x a := by
  unfold TraceState.Live
  rw [h]

/-- Traced states with the same memories agree on the pointers that each
allocation holds. -/
theorem TraceState.ptrsIn_congr {s t : TraceState Mem unit} (h : t.mem = s.mem) :
    t.ptrsIn = s.ptrsIn := by
  funext x a
  unfold TraceState.ptrsIn
  rw [h]

variable (μ)

/-- A live allocation has a handle once it escapes. -/
theorem TraceState.mem_escape {s : TraceState Mem unit} {x : Mem} {a : AllocId}
    (h : s.Live x a) : (x, a) ∈ (s.escape x a).2.escaped := by
  unfold TraceState.escape
  have h' : ((s.mem.mem x).blocks[a]?.map (·.live)) = some true := h
  simp only [h', ↓reduceIte]
  split
  · rename_i k hk
    obtain ⟨hk', hk'', -⟩ := List.idxOf?_eq_some_iff.1 hk
    exact hk'' ▸ List.getElem_mem hk'
  · exact List.mem_append_right _ (List.mem_singleton_self _)

/-- After the pointers' allocations escape, the live allocation of each of
them has a handle. -/
theorem TraceState.mem_escapePtrs (qs : List (Nat × Pointer)) :
    ∀ (t : TraceState Mem unit) {q : Nat × Pointer} {a : AllocId}, q ∈ qs → q.2.prov = some a →
      t.Live (μ q.1) a → (μ q.1, a) ∈ (t.escapePtrs μ qs).escaped := by
  induction qs with
  | nil => intro _ _ _ hq; cases hq
  | cons q' qs ih =>
    intro t q a hq hp hl
    show (μ q.1, a) ∈ ((t.escapePtr μ q').escapePtrs μ qs).escaped
    rcases List.mem_cons.1 hq with rfl | hq
    · have h₁ : (μ q.1, a) ∈ (t.escapePtr μ q).escaped := by
        unfold TraceState.escapePtr
        rw [hp]
        exact TraceState.mem_escape hl
      exact (TraceState.escapePtrs_prefix μ qs _).subset h₁
    · exact ih _ hq hp ((TraceState.live_congr (t.escapePtr_mem μ q') _ _).2 hl)

/-- Every allocation that has a handle after the pointers' allocations
escape is one that had, or the live allocation of one of them. -/
theorem TraceState.escapePtrs_sound (P : Mem × AllocId → Prop) (qs : List (Nat × Pointer)) :
    ∀ t : TraceState Mem unit, (∀ p ∈ t.escaped, P p) →
      (∀ q ∈ qs, ∀ a, q.2.prov = some a → t.Live (μ q.1) a → P (μ q.1, a)) →
        ∀ p ∈ (t.escapePtrs μ qs).escaped, P p := by
  induction qs with
  | nil => intro t ht _; exact ht
  | cons q qs ih =>
    intro t ht hq
    refine ih (t.escapePtr μ q) ?_ fun q' hq' a hp hl => hq q' (List.mem_cons_of_mem _ hq') a hp
      ((TraceState.live_congr (t.escapePtr_mem μ q) _ _).1 hl)
    rcases t.escapePtr_cases μ q with h | ⟨a, hp, hl, -, h⟩ <;> rw [h]
    · exact ht
    · intro p hp'
      rcases List.mem_append.1 hp' with hp' | hp'
      · exact ht p hp'
      · rw [List.mem_singleton.1 hp']
        exact hq q List.mem_cons_self a hp hl

/-- The walk lets escape only what the escaped allocations reach: for a
property of allocations that every escaped allocation has, and that the
live allocation of every pointer that a unit of an allocation with it holds
has, every allocation that has a handle after the walk has it. -/
theorem TraceState.reach_sound (P : Mem × AllocId → Prop) (s₀ : TraceState Mem unit)
    (hP : ∀ x a, P (x, a) → ∀ q ∈ s₀.ptrsIn x a, ∀ b, q.2.prov = some b → s₀.Live (μ q.1) b →
      P (μ q.1, b)) (t : TraceState Mem unit) (k : Nat) :
    t.mem = s₀.mem → (∀ p ∈ t.escaped, P p) → ∀ p ∈ (t.reach μ k).escaped, P p := by
  induction t, k using TraceState.reach.induct μ with
  | case1 t k h ih =>
    intro hm ht
    rw [TraceState.reach]
    simp only [h, ↓reduceDIte]
    refine ih ((TraceState.escapePtrs_mem μ _ t).trans hm) (TraceState.escapePtrs_sound μ P _ t ht
      fun q hq b hp hl => ?_)
    rw [TraceState.ptrsIn_congr hm] at hq
    exact hP _ _ (ht _ (List.getElem_mem h)) q hq b hp ((TraceState.live_congr hm _ _).1 hl)
  | case2 t k h =>
    intro _ ht
    rw [TraceState.reach]
    simpa [h] using ht

/-- What an external call lets escape is reachable: every allocation that
has a handle after the call had escaped, or is reachable from its pointer
arguments. -/
theorem TraceState.escapeCall_sound (s : TraceState Mem unit) (qs : List (Nat × Pointer)) :
    ∀ p ∈ (s.escapeCall μ qs).escaped, s.Reaches μ qs p := by
  refine TraceState.reach_sound μ (s.Reaches μ qs) s
    (fun x a hr q hq b hp hl => .unit hr hq hp hl) _ 0 (TraceState.escapePtrs_mem μ qs s)
    (TraceState.escapePtrs_sound μ _ qs s (fun p hp => .escaped hp) fun q hq a hp hl => ?_)
  exact .arg hq hp hl

/-- The escaped allocations below the place `k` are covered: the live
allocation of each pointer that a unit of one of them holds has a handle. -/
def TraceState.Covered (t : TraceState Mem unit) (k : Nat) : Prop :=
  ∀ j (hj : j < t.escaped.length), j < k → ∀ q ∈ t.ptrsIn t.escaped[j].1 t.escaped[j].2,
    ∀ b, q.2.prov = some b → t.Live (μ q.1) b → (μ q.1, b) ∈ t.escaped

/-- The walk from a place below which the escaped allocations are covered
covers all of them. -/
theorem TraceState.reach_covered (t : TraceState Mem unit) (k : Nat) :
    t.Covered μ k → (t.reach μ k).Covered μ (t.reach μ k).escaped.length := by
  induction t, k using TraceState.reach.induct μ with
  | case1 t k h ih =>
    intro hc
    rw [TraceState.reach]
    simp only [h, ↓reduceDIte]
    apply ih
    have hm := TraceState.escapePtrs_mem μ (t.ptrsIn t.escaped[k].1 t.escaped[k].2) t
    have hpre := TraceState.escapePtrs_prefix μ (t.ptrsIn t.escaped[k].1 t.escaped[k].2) t
    intro j hj hjk q hq b hp hl
    have hjt : j < t.escaped.length := by omega
    have he : (t.escapePtrs μ (t.ptrsIn t.escaped[k].1 t.escaped[k].2)).escaped[j] =
        t.escaped[j] := (List.IsPrefix.getElem hpre hjt).symm
    rw [he, TraceState.ptrsIn_congr hm] at hq
    rw [TraceState.live_congr hm] at hl
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with hjk | rfl
    · exact hpre.subset (hc j hjt hjk q hq b hp hl)
    · exact TraceState.mem_escapePtrs μ _ t hq hp hl
  | case2 t k h =>
    intro hc
    rw [TraceState.reach]
    simp only [h, ↓reduceDIte]
    exact fun j hj _ => hc j hj (by omega)

/-- What an external call lets escape is closed: every allocation reachable
from its pointer arguments, or from the allocations that had escaped, has
a handle after the call. -/
theorem TraceState.escapeCall_closed (s : TraceState Mem unit) (qs : List (Nat × Pointer))
    {p : Mem × AllocId} (h : s.Reaches μ qs p) : p ∈ (s.escapeCall μ qs).escaped := by
  have hc := TraceState.reach_covered μ (s.escapePtrs μ qs) 0 fun _ _ h => absurd h (Nat.not_lt_zero _)
  have hm := s.escapeCall_mem μ qs
  have hpre := ((s.escapePtrs μ qs).reach_mem_prefix μ 0).2
  induction h with
  | escaped hp => exact (s.escapeCall_prefix μ qs).subset hp
  | arg hq hp hl => exact hpre.subset (TraceState.mem_escapePtrs μ qs s hq hp hl)
  | @unit x a n q b _ hq hp hl ih =>
    obtain ⟨j, hj, he⟩ := List.getElem_of_mem ih
    have hq' : (n, q) ∈ (s.escapeCall μ qs).ptrsIn (s.escapeCall μ qs).escaped[j].1
        (s.escapeCall μ qs).escaped[j].2 := by
      rw [TraceState.ptrsIn_congr hm, he]
      exact hq
    exact hc j hj hj _ hq' _ hp ((TraceState.live_congr hm _ _).2 hl)

end Fir
