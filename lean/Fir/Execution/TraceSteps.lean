import Fir.Execution.TraceObligations
import Fir.Execution.MemoryFinite

/-!
# The first steps of a marked trace

A traced run marks each of its steps in its trace (`Fir.Execution.TraceRuns`).
What a marked trace shows in its first _N_ steps is what precedes its step
_N + 1_. Divergence of traced runs compares these: a run diverges silently
after the trace _t_ when, from some budget on, it shows all of _t_ in its
first steps; and it shows an infinite trace when it shows more and more of
it in more and more steps.

This section counts the steps of a marked trace and says how its first steps
behave:

* the first _N_ steps of a marked trace start it, and start its first _N'_
  steps when _N ≤ N'_; the first _N_ steps of the first _N'_ steps are the
  first _N_ steps;
* the first _N_ steps of a marked trace that starts another start the
  other's first _N_ steps; a marked trace with at most _N_ steps is its
  first _N_ steps;
* marked traces that refine each other, a step by a step and an act by an
  act that refines it, have first steps that refine each other.

It also gives the pigeonhole principle that divergence needs: when, at
infinitely many budgets, something lies in one finite list, one member of
the list occurs at infinitely many of them.
-/

namespace Fir

variable {A α : Type}

/-! # Steps -/

/-- The number of steps of a marked trace. -/
def Step.ticks : List (Step A) → Nat
  | [] => 0
  | .tick :: mt => ticks mt + 1
  | .act _ :: mt => ticks mt

/-- The steps of two marked traces, one after the other, add up. -/
theorem Step.ticks_append : ∀ (mt mt' : List (Step A)), ticks (mt ++ mt') = ticks mt + ticks mt'
  | [], _ => by simp [ticks]
  | .tick :: mt, mt' => by simp only [List.cons_append, ticks, ticks_append mt mt']; omega
  | .act _ :: mt, mt' => by simp only [List.cons_append, ticks, ticks_append mt mt']

/-! # First steps -/

/-- The first steps of a marked trace start it. -/
theorem Step.upTo_prefix : ∀ (N : Nat) (mt : List (Step A)), upTo N mt <+: mt
  | _, [] => List.nil_prefix
  | N, .act _ :: mt => (List.prefix_cons_inj _).2 (upTo_prefix N mt)
  | 0, .tick :: _ => List.nil_prefix
  | N + 1, .tick :: mt => (List.prefix_cons_inj _).2 (upTo_prefix N mt)

/-- The first `N` steps start the first `N'` steps when `N ≤ N'`. -/
theorem Step.upTo_mono : ∀ {N N' : Nat}, N ≤ N' → ∀ mt : List (Step A), upTo N mt <+: upTo N' mt
  | _, _, _, [] => List.nil_prefix
  | N, N', h, .act _ :: mt => (List.prefix_cons_inj _).2 (upTo_mono h mt)
  | 0, _, _, .tick :: _ => List.nil_prefix
  | _ + 1, 0, h, _ => absurd h (by omega)
  | N + 1, N' + 1, h, .tick :: mt => (List.prefix_cons_inj _).2 (upTo_mono (by omega) mt)

/-- The first `N` steps of the first `N'` steps are the first `N` steps, when
`N ≤ N'`. -/
theorem Step.upTo_upTo : ∀ {N N' : Nat}, N ≤ N' → ∀ mt : List (Step A),
    upTo N (upTo N' mt) = upTo N mt
  | _, _, _, [] => rfl
  | N, N', h, .act _ :: mt => by simp only [upTo, upTo_upTo h mt]
  | 0, 0, _, .tick :: _ => rfl
  | 0, _ + 1, _, .tick :: _ => rfl
  | _ + 1, 0, h, _ => absurd h (by omega)
  | N + 1, N' + 1, h, .tick :: mt => by simp only [upTo, upTo_upTo (by omega : N ≤ N') mt]

/-- The first steps of a marked trace that starts another start the other's
first steps. -/
theorem Step.upTo_of_prefix : ∀ (N : Nat) {mt mt' : List (Step A)}, mt <+: mt' →
    upTo N mt <+: upTo N mt'
  | _, [], _, _ => by simp only [upTo]; exact List.nil_prefix
  | _, _ :: _, [], h => absurd h.length_le (by simp)
  | N, x :: mt, y :: mt', h => by
    obtain ⟨rfl, hp⟩ := List.cons_prefix_cons.1 h
    match N, x with
    | N, .act _ => exact (List.prefix_cons_inj _).2 (upTo_of_prefix N hp)
    | 0, .tick => exact List.nil_prefix
    | N + 1, .tick => exact (List.prefix_cons_inj _).2 (upTo_of_prefix N hp)

/-- A marked trace with at most `N` steps is its first `N` steps. -/
theorem Step.upTo_of_ticks_le : ∀ {N : Nat} {mt : List (Step A)}, ticks mt ≤ N → upTo N mt = mt
  | _, [], _ => rfl
  | N, .act _ :: mt, h => by simp only [upTo, upTo_of_ticks_le (N := N) (mt := mt) h]
  | 0, .tick :: _, h => absurd h (by simp [ticks])
  | N + 1, .tick :: mt, h => by
    simp only [upTo, upTo_of_ticks_le (N := N) (mt := mt) (by simp only [ticks] at h; omega)]

/-- A marked trace followed by more keeps its first `N` steps when it has
more than `N` steps. -/
theorem Step.upTo_append_of_lt : ∀ {N : Nat} {mt : List (Step A)} (r : List (Step A)),
    N < ticks mt → upTo N (mt ++ r) = upTo N mt
  | _, [], _, h => absurd h (Nat.not_lt_zero _)
  | N, .act _ :: mt, r, h => by
    simp only [List.cons_append, upTo, upTo_append_of_lt (N := N) (mt := mt) r h]
  | 0, .tick :: _, _, _ => rfl
  | N + 1, .tick :: mt, r, h => by
    simp only [List.cons_append, upTo,
      upTo_append_of_lt (N := N) (mt := mt) r (by simp only [ticks] at h; omega)]

/-- The acts of a marked trace that starts another start the other's acts. -/
theorem Step.actsOf_prefix {mt mt' : List (Step A)} (h : mt <+: mt') :
    actsOf mt <+: actsOf mt' := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨actsOf r, by simp [actsOf]⟩

/-- Marked traces that refine each other have first steps that refine each
other. -/
theorem Step.upTo_isRefinedBy [HRefinement A A] : ∀ (N : Nat) {mt mt' : List (Step A)},
    mt ⊑ mt' → upTo N mt ⊑ upTo N mt'
  | _, [], [], _ => trivial
  | N, .act _ :: _, .act _ :: _, ⟨h, hs⟩ => ⟨h, upTo_isRefinedBy N hs⟩
  | 0, .tick :: _, .tick :: _, _ => trivial
  | N + 1, .tick :: _, .tick :: _, ⟨_, hs⟩ => ⟨trivial, upTo_isRefinedBy N hs⟩
  | _, [], _ :: _, h | _, _ :: _, [], h => h.elim
  | _, .tick :: _, .act _ :: _, ⟨h, _⟩ | _, .act _ :: _, .tick :: _, ⟨h, _⟩ => h.elim

/-! # Lists -/

/-- Lists that start each other are equal. -/
theorem List.IsPrefix.antisymm {l l' : List α} (h : l <+: l') (h' : l' <+: l) : l = l' :=
  h.eq_of_length (Nat.le_antisymm h.length_le h'.length_le)

/-- A list that starts another has, at each of its places, the other's
element there. -/
theorem List.IsPrefix.getElem?_some {l l' : List α} (h : l <+: l') {i : Nat} {a : α}
    (ha : l[i]? = some a) : l'[i]? = some a := by
  obtain ⟨r, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 ha).1]
  exact ha

/-- A list refined by a prefix of another is refined by a prefix of each list
that the other starts. -/
theorem List.IsRefinedPrefix.of_prefix [HRefinement α α] {l l' l'' : List α}
    (h : List.IsRefinedPrefix l l') (h' : l' <+: l'') : List.IsRefinedPrefix l l'' := by
  obtain ⟨m, hm, hp⟩ := h
  exact ⟨m, hm, hp.trans h'⟩

/-! # The pigeonhole principle -/

/-- When, at infinitely many budgets `n` (those of which `P` holds), `g n` lies
in the list `L`, some member of `L` is `g n` at infinitely many of them. -/
theorem List.exists_often {P : Nat → Prop} {g : Nat → α} {L : List α}
    (hP : ∀ m, ∃ n, m ≤ n ∧ P n) (hL : ∀ n, P n → g n ∈ L) :
    ∃ a, ∀ m, ∃ n, m ≤ n ∧ P n ∧ g n = a := by
  refine Classical.byContradiction fun hno => ?_
  have hb : ∀ a ∈ L, ∃ m, ∀ n, m ≤ n → P n → g n ≠ a := fun a _ => by
    obtain ⟨m, hm⟩ := Classical.not_forall.1 (not_exists.1 hno a)
    exact ⟨m, fun n hn hp he => hm ⟨n, hn, hp, he⟩⟩
  obtain ⟨m, hm⟩ := List.exists_budget (Q := fun a m => ∀ n, m ≤ n → P n → g n ≠ a)
    (fun _ _ _ hle hq n hn => hq n (Nat.le_trans hle hn)) hb
  obtain ⟨n, hn, hp⟩ := hP m
  exact hm (g n) (hL n hp) n hn hp rfl

end Fir
