import Fir.Execution.TraceFinite

/-!
# Divergence of a traced run, by König's lemma

A target that diverges shows, at every budget, a path that runs out of fuel.
At each budget, refined arguments give a path of the source that runs out of
fuel after acts that the target's refine one by one, in the same steps, or
that hits UB after acts that the target first shows (`Fir.Execution.TraceArgs`).
UB at one budget allows the target's divergence at once. Otherwise the
source's paths at different budgets may show different acts, each refined by
the target's: one trace of the source must serve every budget. Two facts
about the source's run give it:

* _It truncates._ A path that runs out of fuel at a budget is cut, at each
  smaller budget _n_, to a path that runs out of fuel there, whose marked
  trace starts the longer one's and has at most _n_ steps. A call shows no
  step of its own, but the fuel spent between two steps is bounded by a
  number _W_ that depends only on the module, so the cut keeps the longer
  path's first _N_ steps whenever _W(N + 1) ≤ n_.
* _It has finitely many traces at one budget, given the world's answers_:
  the marked traces of the paths at one budget that run out of fuel and
  whose acts agree with an answer stream are among those of a list.

Then:

* _Silent divergence after the trace t._ From some budget on, the target
  shows all of _t_ in its first _N_ steps. Cut at one large budget, the
  source's paths fall in one finite list, so by the pigeonhole principle one
  trace _t₀_ of their first _N_ steps occurs at infinitely many budgets.
  Each smaller budget is served by cutting a path at a larger one, so the
  source diverges silently after _t₀_, which _t_ refines.
* _An infinite trace T._ The target shows at least _k_ acts in its first
  _K(k)_ steps. The first steps of the source's paths at the levels
  _K(0) ≤ K(1) ≤ …_ form a tree with finitely many nodes at each level, and
  infinitely many budgets reach some node at every level. By König's lemma
  it has an infinite branch, which shows the trace _T₀_ that _T_ refines;
  cutting longer paths along the branch serves every budget.
-/

namespace Fir

variable {A O : Type}

/-! # What the source's run must do -/

/-- The run `R` truncates, with at most `W` steps of fuel between two steps
of a path: each path that runs out of fuel at a budget is cut, at each
smaller budget `n`, to a path that runs out of fuel there, whose marked
trace starts the longer one's, has at most `n` steps, and keeps its first
`N` steps whenever `W (N + 1) ≤ n`. -/
structure TRun.Truncates (W : Nat) (R : Nat → TRun A O) : Prop where
  pos : 0 < W
  cut : ∀ {n n' : Nat} {mt' : List (Step A)}, n ≤ n' → R n' (.ok (.ok .fuelExhausted, mt')) →
    ∃ mt, R n (.ok (.ok .fuelExhausted, mt)) ∧ mt <+: mt' ∧ Step.ticks mt ≤ n ∧
      ∀ N, W * (N + 1) ≤ n → Step.upTo N mt = Step.upTo N mt'

/-- The run `R` has finitely many traces at each budget, given the world's
answers: the marked traces of its paths that run out of fuel there, whose
acts agree with an answer stream, are among those of a list. -/
def TRun.FinitelyMany {E Ans : Type} (R : Nat → TRun (Act E Ans) O) : Prop :=
  ∀ n (ans : Nat → Option Ans), ∃ L : List (List (Step (Act E Ans))),
    ∀ mt, R n (.ok (.ok .fuelExhausted, mt)) → Act.Agrees ans (Step.actsOf mt) → mt ∈ L

/-- At every budget, each path of `R'` that runs out of fuel is allowed by a
path of `R` at the same budget: one that runs out of fuel after a marked
trace that its own refines, or UB after a marked trace that it first shows,
refined. -/
def TRun.ExhaustedAllowed [HRefinement A A] (R R' : Nat → TRun A O) : Prop :=
  ∀ n mt', R' n (.ok (.ok .fuelExhausted, mt')) →
    (∃ mt, R n (.ok (.ok .fuelExhausted, mt)) ∧ mt ⊑ mt') ∨
      ∃ r mt, R n (.error (r, mt)) ∧ List.IsRefinedPrefix mt mt'

section

variable [HRefinement A A]

/-- Either the source hits UB after a marked trace that the target's path at
the same budget first shows, refined, or, at every budget, the source has a
path that runs out of fuel after a marked trace that the target's
refines. -/
theorem TRun.ub_or_paths {R R' : Nat → TRun A O} (h : TRun.ExhaustedAllowed R R')
    {Q : Nat → List (Step A) → Prop} (hQ : ∀ n, ∃ mt', R' n (.ok (.ok .fuelExhausted, mt')) ∧ Q n mt') :
    (∃ n r mt mt', R n (.error (r, mt)) ∧ List.IsRefinedPrefix mt mt' ∧ Q n mt') ∨
      ∃ src tgt : Nat → List (Step A), ∀ n, R n (.ok (.ok .fuelExhausted, src n)) ∧
        R' n (.ok (.ok .fuelExhausted, tgt n)) ∧ src n ⊑ tgt n ∧ Q n (tgt n) := by
  refine (Classical.em _).imp id fun hub => ?_
  have hp : ∀ n, ∃ p : List (Step A) × List (Step A), R n (.ok (.ok .fuelExhausted, p.1)) ∧
      R' n (.ok (.ok .fuelExhausted, p.2)) ∧ p.1 ⊑ p.2 ∧ Q n p.2 := fun n => by
    obtain ⟨mt', hx, hq⟩ := hQ n
    rcases h n mt' hx with ⟨mt, hmt, hle⟩ | ⟨r, mt, hr, hle⟩
    · exact ⟨(mt, mt'), hmt, hx, hle, hq⟩
    · exact absurd ⟨n, r, mt, mt', hr, hle, hq⟩ hub
  exact ⟨fun n => (Classical.choose (hp n)).1, fun n => (Classical.choose (hp n)).2,
    fun n => Classical.choose_spec (hp n)⟩

variable [HRefinement O O]

/-- UB of the source after a marked trace that a path of the target first
shows, refined, allows each outcome that shows that path's acts at their
places. -/
theorem TRun.ub_allows {R : Nat → TRun A O} {n : Nat} {r : String} {mt mt' : List (Step A)}
    (hr : R n (.error (r, mt))) (hle : List.IsRefinedPrefix mt mt') {t : TOutcome A O}
    (ht : ∀ i a, (Step.actsOf mt')[i]? = some a → t.act? i = some a) :
    ∃ s, traceObservable R s ∧ s ⊑ t := by
  refine ⟨.ub (Step.actsOf mt) r, ⟨n, mt, hr, rfl⟩, fun i a ha => ?_⟩
  obtain ⟨b, hb, hab⟩ := List.IsRefinedPrefix.getElem? (Step.actsOf_isRefinedPrefix hle) i a ha
  exact ⟨b, ht i b hb, hab⟩

end

/-! # Silent divergence -/

section

variable {E Ans : Type} [HRefinement E E] [HRefinement O O] {W : Nat}
  {R R' : Nat → TRun (Act E Ans) O}

/-- Marked traces that refine each other show as many acts. -/
theorem Step.actsOf_length_eq {mt mt' : List (Step (Act E Ans))} (h : mt ⊑ mt') :
    (Step.actsOf mt).length = (Step.actsOf mt').length :=
  List.IsRefinedBy.length_eq (Step.actsOf_isRefinedBy h)

/-- When the target diverges silently after the trace `tr`, a source that
truncates, has finitely many traces at each budget, and allows, at each
budget, each path of the target that runs out of fuel, diverges silently
after a trace that `tr` refines, or hits UB after acts that `tr` first
shows, refined. -/
theorem TRun.diverge_allowed (hcut : TRun.Truncates W R) (hfin : TRun.FinitelyMany R)
    (hstep : TRun.ExhaustedAllowed R R') {tr : List (Act E Ans)}
    (h : traceObservable R' (.diverge tr)) :
    ∃ s, traceObservable R s ∧ s ⊑ (.diverge tr : TOutcome (Act E Ans) O) := by
  obtain ⟨N, hN⟩ := h
  rcases TRun.ub_or_paths hstep hN with ⟨n, r, mt, mt', hr, hle, hq, -⟩ | ⟨src, tgt, hst⟩
  · exact TRun.ub_allows hr hle fun _ _ ha => List.IsPrefix.getElem?_some hq ha
  -- From `N` on, the target shows `tr` and nothing more; the source shows as many acts.
  have htgt : ∀ n, N ≤ n → Step.actsOf (tgt n) = tr := fun n hn =>
    (List.IsPrefix.antisymm (hst n).2.2.2.1
      ((hst n).2.2.2.2 hn ▸ Step.actsOf_prefix (Step.upTo_prefix N (tgt n))))
  have hsrc : ∀ n, N ≤ n → Step.actsOf (Step.upTo N (src n)) = Step.actsOf (src n) ∧
      Step.actsOf (Step.upTo N (src n)) ⊑ tr := fun n hn => by
    have h₁ := Step.actsOf_isRefinedBy (Step.upTo_isRefinedBy N (hst n).2.2.1)
    rw [(hst n).2.2.2.2 hn] at h₁
    refine ⟨(Step.actsOf_prefix (Step.upTo_prefix N (src n))).eq_of_length ?_, h₁⟩
    rw [List.IsRefinedBy.length_eq h₁, ← htgt n hn, Step.actsOf_length_eq (hst n).2.2.1]
  let ans : Nat → Option Ans := fun i => tr[i]?.map Act.answer
  have hag : ∀ n, Act.Agrees ans (Step.actsOf (src n)) := fun n => by
    refine Act.Agrees.of_isRefinedPrefix (t' := tr) (fun i a ha => by simp [ans, ha]) ?_
    exact ⟨_, Step.actsOf_isRefinedBy (hst n).2.2.1, (hst n).2.2.2.1⟩
  -- At one budget `C`, finitely many cut paths; one first `N` steps occur infinitely often.
  let C := W * (N + 1) + N
  obtain ⟨L, hL⟩ := hfin C ans
  obtain ⟨q, hq⟩ := List.exists_often (P := (C ≤ ·)) (g := fun n => Step.upTo N (src n))
    (L := L.map (Step.upTo N)) (fun m => ⟨max m C, Nat.le_max_left _ _, Nat.le_max_right _ _⟩)
    fun n hn => by
      obtain ⟨mc, hmc, hpre, -, hup⟩ := hcut.cut hn (hst n).1
      exact List.mem_map.2 ⟨mc, hL mc hmc ((hag n).of_prefix (Step.actsOf_prefix hpre)),
        hup N (by omega)⟩
  have hacts : ∀ n, C ≤ n → Step.upTo N (src n) = q → Step.actsOf (src n) = Step.actsOf q :=
    fun n hn he => he ▸ ((hsrc n (by omega)).1).symm
  obtain ⟨n₀, -, hC₀, hq₀⟩ := hq 0
  refine ⟨.diverge (Step.actsOf q), ⟨C, fun n => ?_⟩, hq₀ ▸ (hsrc n₀ (by omega)).2⟩
  obtain ⟨n₂, hn₂, hC₂, hq₂⟩ := hq (max n C)
  obtain ⟨mt, hmt, hpre, -, hup⟩ := hcut.cut (Nat.le_trans (Nat.le_max_left _ _) hn₂) (hst n₂).1
  have hpre' : Step.actsOf mt <+: Step.actsOf q :=
    hacts n₂ hC₂ hq₂ ▸ Step.actsOf_prefix hpre
  refine ⟨mt, hmt, hpre', fun hCn => ?_⟩
  have hN' : Step.actsOf (Step.upTo N mt) = Step.actsOf q := by
    rw [hup N (by omega), hq₂]
  exact List.IsPrefix.antisymm ((Step.actsOf_prefix (Step.upTo_prefix C mt)).trans hpre')
    (hN' ▸ Step.actsOf_prefix (Step.upTo_mono (by omega) mt))

/-! # Acts forever -/

/-- The largest of the first `k + 1` values of `K`. -/
def kmax (K : Nat → Nat) : Nat → Nat
  | 0 => K 0
  | k + 1 => max (kmax K k) (K (k + 1))

/-- The largest of the first values of `K` is at least each of them. -/
theorem le_kmax (K : Nat → Nat) : ∀ k, K k ≤ kmax K k
  | 0 => Nat.le_refl _
  | _ + 1 => Nat.le_max_right _ _

/-- The largest of the first values of `K` grows. -/
theorem kmax_mono (K : Nat → Nat) {k k' : Nat} (h : k ≤ k') : kmax K k ≤ kmax K k' := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (Nat.le_max_left _ _)

/-- When the target shows the infinite trace `T`, a source that truncates,
has finitely many traces at each budget, and allows, at each budget, each
path of the target that runs out of fuel, shows an infinite trace that `T`
refines, act by act, or hits UB after acts that `T` first shows,
refined. -/
theorem TRun.reacts_allowed (hcut : TRun.Truncates W R) (hfin : TRun.FinitelyMany R)
    (hstep : TRun.ExhaustedAllowed R R') {T : Nat → Act E Ans}
    (h : traceObservable R' (.reacts T)) :
    ∃ s, traceObservable R s ∧ s ⊑ (.reacts T : TOutcome (Act E Ans) O) := by
  classical
  obtain ⟨K, hK⟩ := h
  rcases TRun.ub_or_paths hstep hK with ⟨n, r, mt, mt', hr, hle, hq, -⟩ | ⟨src, tgt, hst⟩
  · exact TRun.ub_allows hr hle fun i a ha => by rw [hq i a ha]; rfl
  -- The levels: `K' k` steps, reached at the budget `C k`.
  let K' : Nat → Nat := fun k => kmax K k + k
  have hK'mono : ∀ {k k'}, k ≤ k' → K' k ≤ K' k' := fun h => Nat.add_le_add (kmax_mono K h) h
  let C : Nat → Nat := fun k => W * (K' k + 1)
  have hKC : ∀ k, K' k + 1 ≤ C k := fun k => Nat.le_mul_of_pos_left _ hcut.pos
  let ans : Nat → Option Ans := fun i => some (T i).answer
  have hag : ∀ n, Act.Agrees ans (Step.actsOf (src n)) := fun n i a ha => by
    obtain ⟨b, hb, hab⟩ := List.IsRefinedBy.getElem?_some
      (Step.actsOf_isRefinedBy (hst n).2.2.1) i a ha
    rw [(hst n).2.2.2.1 i b hb] at hab
    exact (congrArg some hab.2).symm
  -- Finitely many first steps at each level, from the budget of the level on.
  have hcand : ∀ k, ∃ L : List (List (Step (Act E Ans))), ∀ n, C k ≤ n → Step.upTo (K' k) (src n) ∈ L :=
    fun k => by
      obtain ⟨L, hL⟩ := hfin (C k) ans
      refine ⟨L.map (Step.upTo (K' k)), fun n hn => ?_⟩
      obtain ⟨mc, hmc, hpre, -, hup⟩ := hcut.cut hn (hst n).1
      exact List.mem_map.2 ⟨mc, hL mc hmc ((hag n).of_prefix (Step.actsOf_prefix hpre)),
        hup (K' k) (Nat.le_refl _)⟩
  -- A node is good when infinitely many budgets reach it.
  let Good : Nat → List (Step (Act E Ans)) → Prop := fun k q =>
    ∀ m, ∃ n, m ≤ n ∧ Step.upTo (K' k) (src n) = q
  have hstart : ∃ q, Good 0 q := by
    obtain ⟨L, hL⟩ := hcand 0
    obtain ⟨q, hq⟩ := List.exists_often (P := (C 0 ≤ ·)) (g := fun n => Step.upTo (K' 0) (src n))
      (fun m => ⟨max m (C 0), Nat.le_max_left _ _, Nat.le_max_right _ _⟩) hL
    exact ⟨q, fun m => let ⟨n, hn, _, he⟩ := hq m; ⟨n, hn, he⟩⟩
  have hnext : ∀ k q, Good k q → ∃ q', Good (k + 1) q' ∧ Step.upTo (K' k) q' = q := by
    intro k q hg
    obtain ⟨L, hL⟩ := hcand (k + 1)
    obtain ⟨q', hq'⟩ := List.exists_often
      (P := fun n => C (k + 1) ≤ n ∧ Step.upTo (K' k) (src n) = q)
      (g := fun n => Step.upTo (K' (k + 1)) (src n))
      (fun m => let ⟨n, hn, he⟩ := hg (max m (C (k + 1)))
        ⟨n, Nat.le_trans (Nat.le_max_left _ _) hn, Nat.le_trans (Nat.le_max_right _ _) hn, he⟩)
      fun n hn => hL n hn.1
    obtain ⟨n₀, -, ⟨-, he₀⟩, hq₀⟩ := hq' 0
    refine ⟨q', fun m => let ⟨n, hn, _, he⟩ := hq' m; ⟨n, hn, he⟩, ?_⟩
    rw [← hq₀, Step.upTo_upTo (hK'mono (Nat.le_succ k)), he₀]
  -- König's lemma: a branch of good nodes, one at each level.
  let seq : Nat → List (Step (Act E Ans)) := fun k => Nat.rec (Classical.choose hstart)
    (fun k q => if hg : Good k q then Classical.choose (hnext k q hg) else q) k
  have hgood : ∀ k, Good k (seq k) := by
    intro k
    induction k with
    | zero => exact Classical.choose_spec hstart
    | succ k ih =>
      show Good (k + 1) (if hg : Good k (seq k) then Classical.choose (hnext k (seq k) hg) else seq k)
      rw [dite_eq_left ih]
      exact (Classical.choose_spec (hnext k (seq k) ih)).1
  have hlink : ∀ k, Step.upTo (K' k) (seq (k + 1)) = seq k := by
    intro k
    show Step.upTo (K' k) (if hg : Good k (seq k) then Classical.choose (hnext k (seq k) hg)
      else seq k) = seq k
    rw [dite_eq_left (hgood k)]
    exact (Classical.choose_spec (hnext k (seq k) (hgood k))).2
  have hchain : ∀ k k', k ≤ k' → Step.upTo (K' k) (seq k') = seq k := by
    intro k k' h
    induction h with
    | refl =>
      obtain ⟨n, -, he⟩ := hgood k 0
      rw [← he, Step.upTo_upTo (Nat.le_refl _)]
    | step hk ih =>
      rename_i k''
      rw [← ih, ← hlink k'', Step.upTo_upTo (hK'mono hk)]
  have hpre : ∀ k k', k ≤ k' → Step.actsOf (seq k) <+: Step.actsOf (seq k') := fun k k' h =>
    hchain k k' h ▸ Step.actsOf_prefix (Step.upTo_prefix _ _)
  have hlen : ∀ k, k ≤ (Step.actsOf (seq k)).length := fun k => by
    obtain ⟨n, hn, he⟩ := hgood k (K' k)
    rw [← he, Step.actsOf_length_eq (Step.upTo_isRefinedBy _ (hst n).2.2.1)]
    have hkK : K k ≤ K' k := Nat.le_trans (le_kmax K k) (Nat.le_add_right _ _)
    exact Nat.le_trans ((hst n).2.2.2.2 k (Nat.le_trans hkK hn))
      (Step.actsOf_prefix (Step.upTo_mono hkK _)).length_le
  -- The branch's trace.
  let T₀ : Nat → Act E Ans := fun i => (Step.actsOf (seq (i + 1)))[i]'(by have := hlen (i + 1); omega)
  have hT₀ : ∀ k i a, (Step.actsOf (seq k))[i]? = some a → a = T₀ i := fun k i a ha => by
    have hi : (Step.actsOf (seq (i + 1)))[i]? = some (T₀ i) := List.getElem?_eq_getElem _
    rcases Nat.le_total k (i + 1) with hk | hk
    · exact Option.some.inj ((List.IsPrefix.getElem?_some (hpre _ _ hk) ha).symm.trans hi)
    · exact Option.some.inj (ha.symm.trans (List.IsPrefix.getElem?_some (hpre _ _ hk) hi))
  have hT₀T : ∀ i, T₀ i ⊑ T i := fun i => by
    obtain ⟨n, -, he⟩ := hgood (i + 1) 0
    have hi : (Step.actsOf (seq (i + 1)))[i]? = some (T₀ i) := List.getElem?_eq_getElem _
    rw [← he] at hi
    obtain ⟨b, hb, hab⟩ := List.IsRefinedBy.getElem?_some
      (Step.actsOf_isRefinedBy (Step.upTo_isRefinedBy _ (hst n).2.2.1)) i _ hi
    rwa [(hst n).2.2.2.1 i b (List.IsPrefix.getElem?_some
      (Step.actsOf_prefix (Step.upTo_prefix _ _)) hb)] at hab
  refine ⟨.reacts T₀, ⟨C, fun n => ?_⟩, hT₀T⟩
  obtain ⟨n₂, hn₂, hq₂⟩ := hgood n n
  obtain ⟨mt, hmt, hpre₂, hticks, hup⟩ := hcut.cut hn₂ (hst n₂).1
  refine ⟨mt, hmt, fun i a ha => hT₀ n i a ?_, fun k hk => ?_⟩
  · have hp : mt <+: seq n := by
      rw [← Step.upTo_of_ticks_le hticks, ← hq₂]
      exact (Step.upTo_of_prefix n hpre₂).trans
        (Step.upTo_mono (Nat.le_add_left _ _) (src n₂))
    exact List.IsPrefix.getElem?_some (Step.actsOf_prefix hp) ha
  · have hkn : k ≤ n := by have := hKC k; have : k ≤ K' k := Nat.le_add_left _ _; omega
    have he : Step.upTo (K' k) mt = seq k := by
      rw [hup (K' k) hk, ← Step.upTo_upTo (hK'mono hkn) (src n₂), hq₂, hchain k n hkn]
    exact Nat.le_trans (hlen k) (he ▸ (Step.actsOf_prefix
      (Step.upTo_mono (Nat.le_trans (Nat.le_succ _) (hKC k)) mt)).length_le)

end

end Fir
