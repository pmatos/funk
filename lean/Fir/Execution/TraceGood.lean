import Fir.Execution.TraceMoveCases
import Fir.Execution.TraceKonig
import Fir.Execution.TraceBlackBox

/-!
# Showing a stream at unboundedly many budgets

A target that diverges, silently or with acts forever, shows a stream of acts
(`TShows`, `Fir.Execution.TraceBranch`): at every budget it has a path that
runs out of fuel, showing acts of the stream within their deadlines. To follow
the target move by move, the proof keeps a weaker form, which a move keeps
with the same deadlines, less the move's steps (`TGood`): for each number `k`
of acts, at unboundedly many budgets, a path that runs out of fuel shows acts
of the stream, and the first `k'` of them within the deadline of `k'`, for
each `k' ≤ k` that the stream has (`TGood.Sees`).

Cutting a path to a smaller budget keeps its first `N` steps only when the
budget is at least `W (N + 1)` (`Fir.Execution.TraceTruncate`). So a run cut
at every budget would need deadlines `W` times longer at each move, and the
deadlines would grow along a branch of moves. Asking for the deadlines only at
unboundedly many budgets, one number of acts at a time, keeps them: a path cut
at a budget large enough for the deadlines of the first `k` acts keeps them.

* A path that goes on by a move after the marked trace `t` sees the stream
  after `t`'s acts, with deadlines less `t`'s steps (`TGood.Sees.shift`).
* So, when infinitely many paths go on by the same move, the configuration it
  goes on to keeps the weaker form (`TGood.after`).
-/

namespace Fir

open Memory

variable {A : Type}

/-! # The stream after a move -/

/-- The stream `S` after its first `a` places. -/
def Stream.drop (S : Nat → Option A) (a : Nat) : Nat → Option A := fun i => S (i + a)

/-- The deadlines `K` after `a` acts and `j` steps. -/
def Stream.dropK (K : Nat → Nat) (a j : Nat) : Nat → Nat := fun k => K (k + a) - j

/-- The marked trace `mt` shows acts of the stream `T`, and its first `k'`
acts within the deadline `K k'`, for each `k' ≤ k` that `T` has. -/
def TGood.Sees (T : Nat → Option A) (K : Nat → Nat) (k : Nat) (mt : List (Step A)) : Prop :=
  Stream.Cons T (Step.actsOf mt) ∧
    ∀ k' ≤ k, Stream.Avail T k' → k' ≤ (Step.actsOf (Step.upTo (K k') mt)).length

/-- The run `R` shows the stream `T` with the deadlines `K` at unboundedly many
budgets, for each number of acts: for each `k` and each budget `B`, it has a
path that runs out of fuel at a budget of at least `B` and sees `T` for `k`
acts. -/
def TGood (R : Nat → List (Step A) → Prop) (T : Nat → Option A) (K : Nat → Nat) : Prop :=
  ∀ k B, ∃ n, B ≤ n ∧ ∃ mt, R n mt ∧ TGood.Sees T K k mt

namespace TGood.Sees

variable {T : Nat → Option A} {K : Nat → Nat}

/-- A trace that sees a stream for `k` acts sees it for fewer. -/
theorem mono {k k' : Nat} {mt : List (Step A)} (h : TGood.Sees T K k mt) (hk : k' ≤ k) :
    TGood.Sees T K k' mt :=
  ⟨h.1, fun k'' hk'' => h.2 k'' (Nat.le_trans hk'' hk)⟩

/-- A trace that sees a stream shows its first acts at their places. -/
theorem cons_prefix {k : Nat} {t mt₁ : List (Step A)} (h : TGood.Sees T K k (t ++ mt₁)) :
    Stream.Cons T (Step.actsOf t) := fun i a ha =>
  h.1 i a (by rw [Step.actsOf_append, List.getElem?_append_left (List.getElem?_eq_some_iff.1 ha).1]; exact ha)

/-- A stream that a trace's first acts start has as many acts more as the
stream after them. -/
theorem avail_of_drop {k : Nat} {t mt₁ : List (Step A)} (h : TGood.Sees T K k (t ++ mt₁)) {x : Nat}
    (hx : Stream.Avail (Stream.drop T (Step.actsOf t).length) x) :
    Stream.Avail T (x + (Step.actsOf t).length) := fun i hi => by
  by_cases hi' : i < (Step.actsOf t).length
  · rw [h.cons_prefix i _ (List.getElem?_eq_getElem hi')]
    rfl
  · have := hx (i - (Step.actsOf t).length) (by omega)
    simp only [Stream.drop] at this
    rwa [Nat.sub_add_cancel (by omega)] at this

/-- A trace that sees a stream, its first acts within their deadlines, has
each deadline after its first acts at least its steps. -/
theorem steps_le {k x : Nat} {t mt₁ : List (Step A)} (h : TGood.Sees T K k (t ++ mt₁))
    (hx : x + (Step.actsOf t).length ≤ k) (havail : Stream.Avail T (x + (Step.actsOf t).length))
    (hlt : K (x + (Step.actsOf t).length) < Step.ticks t) : x = 0 := by
  have h₁ := h.2 _ hx havail
  rw [Step.upTo_append_of_lt mt₁ hlt] at h₁
  have := (Step.actsOf_prefix (Step.upTo_prefix (K (x + (Step.actsOf t).length)) t)).length_le
  omega

/-- A trace that goes on after the marked trace `t` sees the stream after
`t`'s acts, with deadlines less `t`'s steps. -/
theorem shift {k : Nat} {t mt₁ : List (Step A)}
    (h : TGood.Sees T K (k + (Step.actsOf t).length) (t ++ mt₁)) :
    TGood.Sees (Stream.drop T (Step.actsOf t).length)
      (Stream.dropK K (Step.actsOf t).length (Step.ticks t)) k mt₁ := by
  refine ⟨fun i a ha => h.1 (i + (Step.actsOf t).length) a ?_, fun k' hk' havail => ?_⟩
  · rw [Step.actsOf_append, List.getElem?_append_right (by omega)]
    simpa using ha
  have havail' := h.avail_of_drop havail
  have h₁ := h.2 _ (by omega) havail'
  by_cases hle : Step.ticks t ≤ K (k' + (Step.actsOf t).length)
  · rw [Step.upTo_append_of_ticks_le t mt₁ hle, Step.actsOf_append, List.length_append] at h₁
    simp only [Stream.dropK]
    omega
  · exact (h.steps_le (by omega) havail' (by omega)) ▸ Nat.zero_le _

/-- A prefix of a trace that sees a stream for `k` acts, with more steps than
every deadline of at most `k` acts, sees it for `k` acts. -/
theorem of_prefix {k : Nat} {t₀ mt : List (Step A)} (h : TGood.Sees T K k mt) (hp : t₀ <+: mt)
    (hD : kmax K k < Step.ticks t₀) : TGood.Sees T K k t₀ := by
  refine ⟨fun i a ha => h.1 i a (List.IsPrefix.getElem?_some (Step.actsOf_prefix hp) ha),
    fun k' hk' havail => ?_⟩
  obtain ⟨r, rfl⟩ := hp
  have hlt : K k' < Step.ticks t₀ :=
    Nat.lt_of_le_of_lt (Nat.le_trans (le_kmax K k') (kmax_mono K hk')) hD
  have := h.2 k' hk' havail
  rwa [Step.upTo_append_of_lt r hlt] at this

end TGood.Sees

/-- A run that shows a stream at every budget shows it at unboundedly many,
for each number of acts. -/
theorem TGood.ofShows {R : Nat → List (Step A) → Prop} {T : Nat → Option A} {K : Nat → Nat}
    (h : TShows R T K) : TGood R T K := fun k B => by
  obtain ⟨mt, hmt, hc, hk⟩ := h (max B (kmax K k))
  exact ⟨_, Nat.le_max_left _ _, mt, hmt, hc, fun k' hk' havail => hk k' havail
    (Nat.le_trans (Nat.le_trans (le_kmax K k') (kmax_mono K hk')) (Nat.le_max_right _ _))⟩

/-- A run with paths that go on after the marked trace `t` by paths of `R₁`, at
unboundedly many budgets for each number of acts, which see a stream: `R₁`
shows the stream after `t`'s acts, with deadlines less `t`'s steps, `t` shows
the stream's first acts, and each deadline after them is at least `t`'s
steps. -/
theorem TGood.after {R₁ : Nat → List (Step A) → Prop} {T : Nat → Option A} {K : Nat → Nat}
    {t : List (Step A)}
    (h : ∀ k B, ∃ n, B ≤ n ∧ ∃ mt₁, R₁ n mt₁ ∧ TGood.Sees T K (k + (Step.actsOf t).length) (t ++ mt₁)) :
    TGood R₁ (Stream.drop T (Step.actsOf t).length)
        (Stream.dropK K (Step.actsOf t).length (Step.ticks t)) ∧
      Stream.Cons T (Step.actsOf t) ∧
      ∀ x, Stream.Avail T (x + (Step.actsOf t).length) →
        K (x + (Step.actsOf t).length) < Step.ticks t → x = 0 := by
  refine ⟨fun k B => ?_, ?_, fun x havail hlt => ?_⟩
  · obtain ⟨n, hn, mt₁, h₁, hs⟩ := h k B
    exact ⟨n, hn, mt₁, h₁, hs.shift⟩
  · obtain ⟨_, _, mt₁, _, hs⟩ := h 0 0
    exact hs.cons_prefix
  · obtain ⟨_, _, mt₁, _, hs⟩ := h x 0
    exact hs.steps_le (Nat.le_refl _) havail hlt

/-- A trace that shows acts of a stream agrees with the stream's answers. -/
theorem Stream.Cons.agrees {E Ans : Type} {T : Nat → Option (Act E Ans)} {l : List (Act E Ans)}
    (h : Stream.Cons T l) : Act.Agrees (fun i => (T i).map Act.answer) l := fun i a ha => by
  show Option.map Act.answer (T i) = _
  rw [h i a ha]
  rfl

end Fir
