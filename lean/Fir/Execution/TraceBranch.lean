import Fir.Execution.TraceSteps

/-!
# Showing a stream of acts, move by move

Divergence across a black box cannot compare two runs step for step: the two
callees of a black box take different numbers of steps. So the proof follows
one run _move by move_, where a move is one op, the entry into a callee, or a
whole call of a callee that returns. This section is the part of that proof
that knows nothing of ops, only of the marked traces of the paths that run out
of fuel at each budget.

* _A stream of acts._ A trace that may go on forever is a stream: at each
  place, the act there, or none once the trace has ended. A run _shows_ a
  stream, with deadlines `K`, when at every budget it may run out of fuel
  after acts that the stream has at their places, and with at least `k` acts
  in its first `K k` steps whenever the stream has `k` acts and `K k` is at
  most the budget (`TShows`). Silent divergence after a trace and an infinite
  trace are the two ways of showing a stream (`TShows.diverge`,
  `TShows.reacts`).
* _A move._ A run goes on by a move to another run, after the marked trace
  `t` and with `F` steps of fuel, when each of its budgets either is below `F`,
  with a path that has shown part of `t`, or goes on, after `t`, by every path
  of the other run at a smaller budget, at least the budget less `F`
  (`TStep`). A run that a move goes on by shows the stream `t` puts before
  what that run shows (`TShows.step`).
* _A branch._ A sequence of runs, each going on by a move to the next, shows
  the acts of all the moves, one after the other (`TBranch.tShows`): at each
  budget it has a path that starts with every move whose fuel the budget
  covers, and that is a prefix of the moves' marked traces.
-/

namespace Fir

variable {A : Type}

/-! # First steps of a list that starts with a short one -/

/-- The first `N` steps of a marked trace that starts with one of at most `N`
steps are that one, then the first steps of the rest. -/
theorem Step.upTo_append_of_ticks_le : ∀ {N : Nat} (t r : List (Step A)), Step.ticks t ≤ N →
    Step.upTo N (t ++ r) = t ++ Step.upTo (N - Step.ticks t) r
  | _, [], _, _ => by simp [Step.ticks]
  | N, .act _ :: t, r, h => by
    simp only [Step.ticks] at h
    simp only [List.cons_append, Step.upTo, Step.ticks, upTo_append_of_ticks_le t r h]
  | 0, .tick :: _, _, h => absurd h (by simp [Step.ticks])
  | N + 1, .tick :: t, r, h => by
    simp only [Step.ticks] at h
    simp only [List.cons_append, Step.upTo, Step.ticks,
      upTo_append_of_ticks_le t r (by omega : Step.ticks t ≤ N)]
    congr 3
    omega

/-- A marked trace of at most `N` steps that starts another starts its first
`N` steps. -/
theorem Step.prefix_upTo {N : Nat} {t mt : List (Step A)} (h : t <+: mt) (hN : Step.ticks t ≤ N) :
    t <+: Step.upTo N mt := by
  obtain ⟨r, rfl⟩ := h
  rw [Step.upTo_append_of_ticks_le t r hN]
  exact List.prefix_append _ _

/-! # Streams of acts -/

/-- The stream `S` has at least `k` acts. -/
def Stream.Avail (S : Nat → Option A) (k : Nat) : Prop := ∀ i < k, (S i).isSome

/-- The trace `l` shows acts that the stream `S` has at their places. -/
def Stream.Cons (S : Nat → Option A) (l : List A) : Prop := ∀ i a, l[i]? = some a → S i = some a

/-- The stream of the trace `l`, then the stream `S`. -/
def Stream.cat (l : List A) (S : Nat → Option A) : Nat → Option A :=
  fun i => if i < l.length then l[i]? else S (i - l.length)

/-- A trace, then a trace that shows acts of a stream, shows acts of the
first trace's stream, then that stream. -/
theorem Stream.Cons.cat {S : Nat → Option A} {l m : List A} (h : Stream.Cons S m) :
    Stream.Cons (Stream.cat l S) (l ++ m) := fun i a ha => by
  unfold Stream.cat
  by_cases hi : i < l.length
  · rw [ite_eq_left hi]
    rwa [List.getElem?_append_left hi] at ha
  · rw [ite_eq_right hi]
    rw [List.getElem?_append_right (by omega)] at ha
    exact h _ _ ha

/-- A prefix of a trace shows acts of the trace's stream, then any stream. -/
theorem Stream.Cons.cat_prefix {S : Nat → Option A} {l m : List A} (h : m <+: l) :
    Stream.Cons (Stream.cat l S) m := fun i a ha => by
  have ha' := List.IsPrefix.getElem?_some h ha
  have hi : i < l.length := (List.getElem?_eq_some_iff.1 ha').1
  unfold Stream.cat
  rw [ite_eq_left hi]
  exact ha'

/-- A stream after a trace with `k` acts in all has at least `k` less than
that many in the stream. -/
theorem Stream.Avail.of_cat {S : Nat → Option A} {l : List A} {k : Nat}
    (h : Stream.Avail (Stream.cat l S) k) : Stream.Avail S (k - l.length) := fun i hi => by
  have := h (i + l.length) (by omega)
  unfold Stream.cat at this
  rwa [ite_eq_right (by omega), Nat.add_sub_cancel] at this

/-! # Showing a stream -/

/-- The run `R`, given by the marked traces of its paths that run out of fuel
at each budget, shows the stream `S` with the deadlines `K`: at every budget it
may run out of fuel after acts that `S` has at their places, with at least `k`
acts in its first `K k` steps whenever `S` has `k` acts and `K k` is at most
the budget. -/
def TShows (R : Nat → List (Step A) → Prop) (S : Nat → Option A) (K : Nat → Nat) : Prop :=
  ∀ n, ∃ mt, R n mt ∧ Stream.Cons S (Step.actsOf mt) ∧
    ∀ k, Stream.Avail S k → K k ≤ n → k ≤ (Step.actsOf (Step.upTo (K k) mt)).length

/-- The run `R` goes on by a move to the run `R₁`, after the marked trace `t`
and with `F` steps of fuel, of which `t` takes at most all: at each budget `n`,
either `n` is below `F` and `R` has a path that has shown part of `t`, or `R`
goes on, after `t`, by every path of `R₁` at a smaller budget, at least
`n - F`. -/
structure TStep (R R₁ : Nat → List (Step A) → Prop) (t : List (Step A)) (F : Nat) : Prop where
  ticks_le : Step.ticks t ≤ F
  go : ∀ n, (n < F ∧ ∃ mt, R n mt ∧ mt <+: t) ∨
    ∃ n₁ < n, n ≤ n₁ + F ∧ ∀ mt₁, R₁ n₁ mt₁ → R n (t ++ mt₁)

/-- The deadlines of a run that goes on by a move, after the acts `l` of its
marked trace and with `F` steps of fuel, to a run with the deadlines `K`. -/
def TStep.deadline (l : List A) (F : Nat) (K : Nat → Nat) (k : Nat) : Nat :=
  if k ≤ l.length then F else F + K (k - l.length)

/-- A run that goes on by a move shows the move's acts, then what the run it
goes on by shows. -/
theorem TShows.step {R R₁ : Nat → List (Step A) → Prop} {t : List (Step A)} {F : Nat}
    {S : Nat → Option A} {K : Nat → Nat} (h : TStep R R₁ t F) (h₁ : TShows R₁ S K) :
    TShows R (Stream.cat (Step.actsOf t) S) (TStep.deadline (Step.actsOf t) F K) := by
  intro n
  rcases h.go n with ⟨hn, mt, hmt, hp⟩ | ⟨n₁, -, hle, hR⟩
  · refine ⟨mt, hmt, Stream.Cons.cat_prefix (Step.actsOf_prefix hp), fun k _ hk => ?_⟩
    unfold TStep.deadline at hk
    split at hk <;> omega
  · obtain ⟨mt₁, hmt₁, hc, hk⟩ := h₁ n₁
    refine ⟨t ++ mt₁, hR _ hmt₁, ?_, fun k havail hk' => ?_⟩
    · have e : Step.actsOf (t ++ mt₁) = Step.actsOf t ++ Step.actsOf mt₁ := by simp [Step.actsOf]
      rw [e]
      exact hc.cat
    have := h.ticks_le
    have hpre : t <+: Step.upTo (TStep.deadline (Step.actsOf t) F K k) (t ++ mt₁) :=
      Step.prefix_upTo (List.prefix_append _ _) (by unfold TStep.deadline; split <;> omega)
    unfold TStep.deadline at hk' ⊢
    split
    · have := (Step.actsOf_prefix hpre).length_le
      unfold TStep.deadline at this
      rw [ite_eq_left ‹_›] at this
      omega
    · rw [ite_eq_right ‹_›] at hk'
      have hk₁ := hk _ havail.of_cat (by omega)
      have e : ∀ l : List (Step A), Step.actsOf (t ++ l) = Step.actsOf t ++ Step.actsOf l := by
        simp [Step.actsOf]
      rw [Step.upTo_append_of_ticks_le t mt₁ (by omega), e, List.length_append]
      have := (Step.actsOf_prefix (Step.upTo_mono (N := K (k - (Step.actsOf t).length))
        (N' := F + K (k - (Step.actsOf t).length) - Step.ticks t) (by omega) mt₁)).length_le
      omega

/-! # A branch of moves -/

/-- The marked traces of `j` moves of a branch, from its run `i`. -/
def TBranch.pre (t : Nat → List (Step A)) : Nat → Nat → List (Step A)
  | _, 0 => []
  | i, j + 1 => t i ++ pre t (i + 1) j

/-- The fuel of `j` moves of a branch, from its run `i`. -/
def TBranch.fuel (F : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | i, j + 1 => F i + fuel F (i + 1) j

/-- More moves of a branch go on from fewer. -/
theorem TBranch.pre_prefix (t : Nat → List (Step A)) :
    ∀ (i j l : Nat), TBranch.pre t i j <+: TBranch.pre t i (j + l)
  | _, 0, _ => List.nil_prefix
  | i, j + 1, l => by
    rw [Nat.add_right_comm]
    exact (List.prefix_append_right_inj _).2 (pre_prefix t (i + 1) j l)

/-- Moves take at most their fuel in steps. -/
theorem TBranch.ticks_pre_le {t : Nat → List (Step A)} {F : Nat → Nat}
    (h : ∀ i, Step.ticks (t i) ≤ F i) : ∀ i j, Step.ticks (TBranch.pre t i j) ≤ TBranch.fuel F i j
  | _, 0 => by simp [TBranch.pre, TBranch.fuel, Step.ticks]
  | i, j + 1 => by
    simp only [TBranch.pre, TBranch.fuel, Step.ticks_append]
    have := ticks_pre_le h (i + 1) j
    have := h i
    omega

/-- A branch of runs, each going on by a move to the next, has at each budget
a path that starts with every few moves whose fuel the budget covers, and is
a prefix of the marked traces of some moves. -/
theorem TBranch.realized {R : Nat → Nat → List (Step A) → Prop} {t : Nat → List (Step A)}
    {F : Nat → Nat} (h : ∀ i, TStep (R i) (R (i + 1)) (t i) (F i)) (n : Nat) :
    ∀ i, ∃ mt, R i n mt ∧ (∃ j, mt <+: TBranch.pre t i j) ∧
      ∀ j, TBranch.fuel F i j ≤ n → TBranch.pre t i j <+: mt := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i
    rcases (h i).go n with ⟨hn, mt, hmt, hp⟩ | ⟨n₁, hlt, hle, hR⟩
    · refine ⟨mt, hmt, ⟨1, by simpa [TBranch.pre] using hp⟩, fun j hj => ?_⟩
      cases j with
      | zero => exact List.nil_prefix
      | succ j => simp only [TBranch.fuel] at hj; omega
    · obtain ⟨mt₁, hmt₁, ⟨j₁, hj₁⟩, hpre⟩ := ih n₁ hlt (i + 1)
      refine ⟨t i ++ mt₁, hR _ hmt₁, ⟨j₁ + 1, (List.prefix_append_right_inj _).2 hj₁⟩,
        fun j hj => ?_⟩
      cases j with
      | zero => exact List.nil_prefix
      | succ j =>
        simp only [TBranch.fuel] at hj
        exact (List.prefix_append_right_inj _).2 (hpre j (by omega))

open Classical in
/-- The acts of all the moves of a branch from its run `i`, one after the
other: the act at each place that some moves reach. -/
noncomputable def TBranch.acts (t : Nat → List (Step A)) (i : Nat) : Nat → Option A := fun p =>
  if h : ∃ j, p < (Step.actsOf (TBranch.pre t i j)).length then
    (Step.actsOf (TBranch.pre t i (Classical.choose h)))[p]?
  else none

/-- The acts of some moves of a branch are its acts at their places. -/
theorem TBranch.acts_eq {t : Nat → List (Step A)} {i j p : Nat} {a : A}
    (h : (Step.actsOf (TBranch.pre t i j))[p]? = some a) : TBranch.acts t i p = some a := by
  have hex : ∃ j, p < (Step.actsOf (TBranch.pre t i j)).length :=
    ⟨j, (List.getElem?_eq_some_iff.1 h).1⟩
  unfold TBranch.acts
  rw [dite_eq_left hex]
  have hj' := Classical.choose_spec hex
  rcases Nat.le_total j (Classical.choose hex) with hle | hle
  · obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le hle
    rw [hl]
    exact List.IsPrefix.getElem?_some (Step.actsOf_prefix (TBranch.pre_prefix t i j l)) h
  · obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le hle
    obtain ⟨b, hb⟩ : ∃ b, (Step.actsOf (TBranch.pre t i (Classical.choose hex)))[p]? = some b :=
      ⟨_, List.getElem?_eq_getElem hj'⟩
    have := List.IsPrefix.getElem?_some
      (Step.actsOf_prefix (TBranch.pre_prefix t i (Classical.choose hex) l)) hb
    rw [← hl, h] at this
    rw [hb, this]

/-- An act of a branch is the act of some of its moves at its place. -/
theorem TBranch.acts_some {t : Nat → List (Step A)} {i p : Nat} {a : A}
    (h : TBranch.acts t i p = some a) : ∃ j, (Step.actsOf (TBranch.pre t i j))[p]? = some a := by
  unfold TBranch.acts at h
  split at h
  · exact ⟨_, h⟩
  · cases h

open Classical in
/-- The deadlines of a branch from its run `i`: for `k` acts, the fuel of some
moves that show them. -/
noncomputable def TBranch.deadline (t : Nat → List (Step A)) (F : Nat → Nat) (i k : Nat) : Nat :=
  if h : ∃ j, k ≤ (Step.actsOf (TBranch.pre t i j)).length then TBranch.fuel F i (Classical.choose h)
  else 0

/-- A branch of runs, each going on by a move to the next, shows from each of
its runs the acts of all the moves from it, one after the other. -/
theorem TBranch.tShows {R : Nat → Nat → List (Step A) → Prop} {t : Nat → List (Step A)}
    {F : Nat → Nat} (h : ∀ i, TStep (R i) (R (i + 1)) (t i) (F i)) (i : Nat) :
    TShows (R i) (TBranch.acts t i) (TBranch.deadline t F i) := by
  intro n
  obtain ⟨mt, hmt, ⟨j₀, hj₀⟩, hpre⟩ := TBranch.realized h n i
  refine ⟨mt, hmt, fun p a ha => TBranch.acts_eq (List.IsPrefix.getElem?_some
    (Step.actsOf_prefix hj₀) ha), fun k havail hk => ?_⟩
  cases k with
  | zero => exact Nat.zero_le _
  | succ k =>
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (havail k (Nat.lt_succ_self k))
    obtain ⟨j, hj⟩ := TBranch.acts_some ha
    have hex : ∃ j, k + 1 ≤ (Step.actsOf (TBranch.pre t i j)).length :=
      ⟨j, (List.getElem?_eq_some_iff.1 hj).1⟩
    unfold TBranch.deadline at hk ⊢
    rw [dite_eq_left hex] at hk ⊢
    have hp := Step.prefix_upTo (hpre _ hk) (TBranch.ticks_pre_le (fun i => (h i).ticks_le) i _)
    exact Nat.le_trans (Classical.choose_spec hex) (Step.actsOf_prefix hp).length_le

end Fir
