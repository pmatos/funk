import Fir.Execution.TraceTargetBranch

/-!
# Showing a stream, as divergence

Silent divergence after the trace `tr` and the infinite trace `T` are the two
ways a traced run may show a stream of acts at every budget (`TShows`,
`Fir.Execution.TraceBranch`): the stream of `tr`, which ends, and the stream of
`T`, which does not (`TOutcome.act?`).

* A run that diverges, silently or with acts forever, shows the stream of its
  outcome (`TShows.ofObservable`).
* A run that shows a closed stream diverges: silently after the stream's acts
  when the stream ends, with the stream as its infinite trace when it does not
  (`TShows.toObservable`).
* An outcome that diverges is refined by another when their streams are: the
  same places have acts, each act refined by the other's at its place
  (`TOutcome.isRefinedBy_of_stream`).
-/

namespace Fir

variable {A O : Type}

/-! # Streams that refine others -/

section

variable [HRefinement A A]

/-- The stream `S` is refined by the stream `T`: the same places have acts, and
each act of `S` is refined by `T`'s at its place. -/
def Stream.IsRefinedBy (S T : Nat → Option A) : Prop :=
  ∀ i, (S i = none ↔ T i = none) ∧ ∀ a b, S i = some a → T i = some b → a ⊑ b

/-- The trace `l` is refined by the first acts of the stream `T`, each act at
its place. -/
def Stream.ShowsRefined (l : List A) (T : Nat → Option A) : Prop :=
  ∀ i a, l[i]? = some a → ∃ b, T i = some b ∧ a ⊑ b

/-- A trace refined by another, then a stream refined by another, is refined
by the other trace, then the other stream. -/
theorem Stream.IsRefinedBy.cat {S T : Nat → Option A} {l l' : List A} (hl : l ⊑ l')
    (h : Stream.IsRefinedBy S T) : Stream.IsRefinedBy (Stream.cat l S) (Stream.cat l' T) := by
  have hlen := List.IsRefinedBy.length_eq hl
  intro i
  unfold Stream.cat
  rw [hlen]
  by_cases hi : i < l'.length
  · rw [ite_eq_left hi, ite_eq_left hi]
    rcases List.IsRefinedBy.getElem? hl i with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, hab⟩
    · rw [h₁, h₂]
      exact ⟨Iff.rfl, (fun _ _ h => nomatch h)⟩
    · rw [h₁, h₂]
      exact ⟨⟨(fun h => nomatch h), (fun h => nomatch h)⟩, fun a' b' ha hb => by
        cases ha
        cases hb
        exact hab⟩
  · rw [ite_eq_right hi, ite_eq_right hi]
    exact h _

/-- A trace refined by another, then a trace refined by the first acts of a
stream, is refined by the other trace, then that stream. -/
theorem Stream.ShowsRefined.cat {T : Nat → Option A} {l l' m : List A} (hl : l ⊑ l')
    (h : Stream.ShowsRefined m T) : Stream.ShowsRefined (l ++ m) (Stream.cat l' T) := fun i a ha => by
  have hlen := List.IsRefinedBy.length_eq hl
  unfold Stream.cat
  by_cases hi : i < l.length
  · rw [List.getElem?_append_left hi] at ha
    obtain ⟨b, hb, hab⟩ := List.IsRefinedBy.getElem?_some hl i a ha
    exact ⟨b, by rw [ite_eq_left (hlen ▸ hi)]; exact hb, hab⟩
  · rw [List.getElem?_append_right (by omega)] at ha
    obtain ⟨b, hb, hab⟩ := h _ _ ha
    exact ⟨b, by rw [ite_eq_right (hlen ▸ hi), ← hlen]; exact hb, hab⟩

/-- Lists that have acts at the same places, each refined by the other's at its
place, refine each other. -/
theorem List.isRefinedBy_of_getElem? : ∀ {l l' : List A},
    (∀ i : Nat, (l[i]? = none ↔ l'[i]? = none) ∧ ∀ a b, l[i]? = some a → l'[i]? = some b → a ⊑ b) →
    l ⊑ l'
  | [], [], _ => trivial
  | [], _ :: _, h => by have := (h 0).1; simp at this
  | _ :: _, [], h => by have := (h 0).1; simp at this
  | a :: l, b :: l', h => ⟨(h 0).2 a b rfl rfl, List.isRefinedBy_of_getElem? fun i =>
      ⟨by simpa using (h (i + 1)).1, fun a b ha hb => (h (i + 1)).2 a b (by simpa using ha)
        (by simpa using hb)⟩⟩

end

/-! # Divergence as a stream -/

/-- The outcome `t` diverges, silently or with acts forever. -/
def TOutcome.Diverges : TOutcome A O → Prop
  | .diverge _ | .reacts _ => True
  | _ => False

/-- The stream of an outcome that diverges is closed. -/
theorem TOutcome.act?_closed : ∀ {t : TOutcome A O}, t.Diverges → Stream.Closed t.act?
  | .diverge tr, _ => fun i hi => by
    simp only [TOutcome.act?] at hi ⊢
    have := (List.getElem?_eq_some_iff.1 (Option.some_get hi).symm).1
    exact Option.isSome_iff_exists.2 ⟨_, List.getElem?_eq_getElem (by omega)⟩
  | .reacts _, _ => fun _ _ => rfl

variable (R : Nat → TRun A O)

/-- The marked traces of a run's paths that run out of fuel at each budget. -/
def TRun.exh (n : Nat) (mt : List (Step A)) : Prop := R n (.ok (.ok .fuelExhausted, mt))

variable {R}

/-- A run that diverges, silently or with acts forever, shows its outcome's
stream at every budget. -/
theorem TShows.ofObservable : ∀ {t : TOutcome A O}, traceObservable R t → t.Diverges →
    ∃ K, TShows (TRun.exh R) t.act? K
  | .diverge tr, ⟨N, hN⟩, _ => ⟨fun _ => N, fun n => by
      obtain ⟨mt, hmt, hp, he⟩ := hN n
      refine ⟨mt, hmt, fun i a ha => List.IsPrefix.getElem?_some hp ha, fun k hk hn => ?_⟩
      rw [he hn]
      refine Nat.le_of_not_lt fun hlt => ?_
      have := hk tr.length hlt
      simp [TOutcome.act?] at this⟩
  | .reacts T, ⟨K, hK⟩, _ => ⟨K, fun n => by
      obtain ⟨mt, hmt, hc, hk⟩ := hK n
      exact ⟨mt, hmt, fun i a ha => by rw [hc i a ha]; rfl, fun k _ hn => hk k hn⟩⟩
  | .ret _ _, _, h | .ub _ _, _, h => h.elim

/-- A property of some number holds of a least one. -/
theorem Nat.exists_least {P : Nat → Prop} (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m < n, ¬ P m := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hm : ∃ m < n, P m
    · obtain ⟨m, hm, hp⟩ := hm
      exact ih m hm hp
    · exact ⟨n, hn, fun m hlt hp => hm ⟨m, hlt, hp⟩⟩

/-- A stream with acts at its first `q` places has them as those of a list. -/
theorem Stream.exists_list (S : Nat → Option A) :
    ∀ q, Stream.Avail S q → ∃ tr : List A, tr.length = q ∧ ∀ i < q, tr[i]? = S i
  | 0, _ => ⟨[], rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | q + 1, h => by
    obtain ⟨tr, hlen, htr⟩ := Stream.exists_list S q fun i hi => h i (by omega)
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (h q (Nat.lt_succ_self q))
    refine ⟨tr ++ [a], by simp [hlen], fun i hi => ?_⟩
    by_cases hiq : i < q
    · rw [List.getElem?_append_left (by omega)]
      exact htr i hiq
    · have : i = q := by omega
      subst this
      rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self, ha]
      rfl

/-- A closed stream that ends at a place has acts exactly at the places of a
list. -/
theorem Stream.Closed.eq_list {S : Nat → Option A} (h : Stream.Closed S) {p : Nat}
    (hp : S p = none) : ∃ tr : List A, ∀ i, S i = tr[i]? := by
  obtain ⟨q, hq, hmin⟩ := Nat.exists_least (P := fun n => S n = none) ⟨p, hp⟩
  obtain ⟨tr, hlen, htr⟩ := Stream.exists_list S q fun i hi => by
    cases hs : S i with
    | none => exact absurd hs (hmin i hi)
    | some _ => rfl
  refine ⟨tr, fun i => ?_⟩
  by_cases hi : i < q
  · exact (htr i hi).symm
  · rw [List.getElem?_eq_none (by omega)]
    cases hs : S i with
    | none => rfl
    | some a =>
      have := Stream.Closed.avail h hs q (by omega)
      rw [hq] at this
      cases this

/-- A run that shows a closed stream at every budget diverges: silently after
the stream's acts when it ends, with the stream as its infinite trace when it
does not. -/
theorem TShows.toObservable {S : Nat → Option A} {K : Nat → Nat} (h : TShows (TRun.exh R) S K)
    (hcl : Stream.Closed S) :
    ∃ t, traceObservable R t ∧ t.Diverges ∧ ∀ i, t.act? i = S i := by
  by_cases hend : ∃ p, S p = none
  · obtain ⟨p, hp⟩ := hend
    obtain ⟨tr, htr⟩ := hcl.eq_list hp
    refine ⟨.diverge tr, ⟨K tr.length, fun n => ?_⟩, trivial, fun i => (htr i).symm⟩
    obtain ⟨mt, hmt, hc, hk⟩ := h n
    have hpre : Step.actsOf mt <+: tr :=
      List.prefix_iff_getElem?.2 fun i hi => by
        rw [← htr]; exact hc i _ (List.getElem?_eq_getElem hi)
    refine ⟨mt, hmt, hpre, fun hn => ?_⟩
    have havail : Stream.Avail S tr.length := fun i hi => by
      rw [htr]
      exact Option.isSome_iff_exists.2 ⟨_, List.getElem?_eq_getElem hi⟩
    have hle := hk _ havail hn
    exact ((Step.actsOf_prefix (Step.upTo_prefix _ mt)).trans hpre).eq_of_length_le hle
  · have hs : ∀ i, (S i).isSome := fun i => by
      cases hSi : S i with
      | none => exact absurd ⟨i, hSi⟩ hend
      | some _ => rfl
    refine ⟨.reacts fun i => (S i).get (hs i), ⟨K, fun n => ?_⟩, trivial,
      fun i => by simp [TOutcome.act?]⟩
    obtain ⟨mt, hmt, hc, hk⟩ := h n
    refine ⟨mt, hmt, fun i a ha => ?_, fun k hk' => hk k (fun i _ => hs i) hk'⟩
    simp [hc i a ha]

variable [HRefinement A A] [HRefinement O O]

/-- An outcome that diverges is refined by another that diverges when their
streams are. -/
theorem TOutcome.isRefinedBy_of_stream : ∀ {s t : TOutcome A O}, s.Diverges → t.Diverges →
    Stream.IsRefinedBy s.act? t.act? → s ⊑ t
  | .diverge tr, .diverge tr', _, _, h => List.isRefinedBy_of_getElem? h
  | .reacts _, .reacts _, _, _, h => fun i => (h i).2 _ _ rfl rfl
  | .diverge tr, .reacts _, _, _, h => by
    have := (h tr.length).1
    simp [TOutcome.act?] at this
  | .reacts _, .diverge tr', _, _, h => by
    have := (h tr'.length).1
    simp [TOutcome.act?] at this
  | .ret _ _, _, hs, _, _ | .ub _ _, _, hs, _, _ => hs.elim
  | .diverge _, .ret _ _, _, ht, _ | .diverge _, .ub _ _, _, ht, _
  | .reacts _, .ret _ _, _, ht, _ | .reacts _, .ub _ _, _, ht, _ => ht.elim

/-- The streams of two outcomes that diverge, one refined by the other, refine
each other. -/
theorem TOutcome.stream_isRefinedBy : ∀ {s t : TOutcome A O}, s.Diverges → t.Diverges → s ⊑ t →
    Stream.IsRefinedBy s.act? t.act?
  | .diverge tr, .diverge tr', _, _, h => fun i => by
    rcases List.IsRefinedBy.getElem? h i with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, hab⟩
    · simp only [TOutcome.act?]
      rw [h₁, h₂]
      exact ⟨Iff.rfl, (fun _ _ h => nomatch h)⟩
    · simp only [TOutcome.act?]
      rw [h₁, h₂]
      exact ⟨⟨(fun h => nomatch h), (fun h => nomatch h)⟩, fun a' b' ha hb => by
        cases ha
        cases hb
        exact hab⟩
  | .reacts _, .reacts _, _, _, h => fun i =>
    ⟨⟨(fun h => nomatch h), (fun h => nomatch h)⟩, fun a b ha hb => by
      cases ha
      cases hb
      exact h i⟩
  | .ret _ _, _, hs, _, _ | .ub _ _, _, hs, _, _ => hs.elim
  | .diverge _, .ret _ _, _, ht, _ | .diverge _, .ub _ _, _, ht, _
  | .reacts _, .ret _ _, _, ht, _ | .reacts _, .ub _ _, _, ht, _ => ht.elim
  | .diverge _, .reacts _, _, _, h | .reacts _, .diverge _, _, _, h => (h : False).elim

end Fir
