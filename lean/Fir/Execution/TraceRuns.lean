import Fir.Execution.TraceMonad

/-!
# Traced runs

A traced run marks its steps. Before an op runs by its dialect's rule, the
run shows a _step_, a mark in its trace that the world never sees. So the
trace of a path tells, of each act, how many steps the path had taken when
it showed it. A traced run at one budget is the set of the ways it may end,
each with its marked trace: with a result, or stuck, or with UB and its
reason.

Its traced observable behaviour is what it shows over every budget. The
acts of a marked trace are its trace; the steps only date them.

* A return or UB, after a finite trace, that some budget reaches.
* Silent divergence after the finite trace _t_: for some number _N_, at
  every budget from _N_ on the run can run out of fuel having shown _t_,
  all of it in its first _N_ steps; and at every budget it can run out of
  fuel having shown a prefix of _t_.
* An infinite trace _T_: there are numbers of steps _K(k)_ such that at
  every budget _n_ the run can run out of fuel having shown a prefix of _T_,
  with at least _k_ acts in its first _K(k)_ steps whenever _K(k) ≤ n_.

Without the steps, a run that can return arbitrarily late after its last
act could not be told apart from one that falls silent after it, nor a run
that can show arbitrarily many acts before it returns from one that shows
acts forever: at each budget both can run out of fuel after the same acts.
The steps tell them apart. When every choice has finitely many options, the
paths that meet one of these conditions at every budget are the prefixes of
an infinite path, by König's lemma, and that path shows _t_ and then falls
silent, or shows _T_. An event may have infinitely many answers, so an
event's answers count as a choice here too.

A run with no act, whose paths end as a run of the set monad, has the
observable behaviour of that run, each outcome with an empty trace, and
divergence silent from the start; so refinement of such traced runs is
refinement of the runs.

A dialect's events, and the traced runs of its functions, are in
`Fir.Execution.TraceDialect`.
-/

namespace Fir

/-! # Marked traces -/

/-- An element of a marked trace: a step of the run, or an act. -/
inductive Step (A : Type) where
  | tick
  | act (a : A)

variable {A O : Type}

/-- The acts of an element of a marked trace: none for a step. -/
def Step.acts : Step A → List A
  | .tick => []
  | .act a => [a]

/-- The acts of a marked trace: its trace. -/
def Step.actsOf (mt : List (Step A)) : List A := mt.flatMap Step.acts

/-- What a marked trace shows in its first `N` steps: its elements before its
step `N + 1`. -/
def Step.upTo : Nat → List (Step A) → List (Step A)
  | _, [] => []
  | N, .act a :: mt => .act a :: upTo N mt
  | 0, .tick :: _ => []
  | N + 1, .tick :: mt => .tick :: upTo N mt

/-- What a marked trace shows in its first steps is a prefix of what it
shows. -/
theorem Step.actsOf_upTo_prefix : ∀ (N : Nat) (mt : List (Step A)),
    Step.actsOf (Step.upTo N mt) <+: Step.actsOf mt
  | _, [] => List.prefix_refl []
  | N, .act a :: mt => by
    simpa [upTo, actsOf, acts] using actsOf_upTo_prefix N mt
  | 0, .tick :: mt => by simp [upTo, actsOf]
  | N + 1, .tick :: mt => by
    simpa [upTo, actsOf, acts] using actsOf_upTo_prefix N mt

/-- A marked trace with no act shows none in its first steps. -/
theorem Step.actsOf_upTo_eq_nil {mt : List (Step A)} (h : Step.actsOf mt = []) (N : Nat) :
    Step.actsOf (Step.upTo N mt) = [] := by
  obtain ⟨t, ht⟩ := Step.actsOf_upTo_prefix N mt
  rw [h] at ht
  exact (List.append_eq_nil_iff.mp ht).1

/-! # Traced runs and their behaviour -/

/-- A traced run at one budget: the set of the ways it may end, each with its
marked trace. A path ends with a result or stuck, or with UB and its
reason. -/
abbrev TRun (A O : Type) : Type :=
  Paths (Except (String × List (Step A)) (Except Stuck (Result O) × List (Step A)))

/-- The traced observable behaviour of a run that takes fuel: each return and
UB that some budget reaches, with its trace; silent divergence after a
finite trace that the run shows within a bounded number of steps; and each
infinite trace that the run shows more of in a bounded number of steps as
its budget grows. -/
def traceObservable (run : Nat → TRun A O) : TBehaviour A O
  | .ret tr o => ∃ n mt, run n (.ok (.ok (.ret o), mt)) ∧ Step.actsOf mt = tr
  | .ub tr r => ∃ n mt, run n (.error (r, mt)) ∧ Step.actsOf mt = tr
  | .diverge tr => ∃ N, ∀ n, ∃ mt, run n (.ok (.ok .fuelExhausted, mt)) ∧
      Step.actsOf mt <+: tr ∧ (N ≤ n → Step.actsOf (Step.upTo N mt) = tr)
  | .reacts T => ∃ K : Nat → Nat, ∀ n, ∃ mt, run n (.ok (.ok .fuelExhausted, mt)) ∧
      (∀ i a, (Step.actsOf mt)[i]? = some a → a = T i) ∧
      ∀ k, K k ≤ n → k ≤ (Step.actsOf (Step.upTo (K k) mt)).length

/-- The traced run `R` shows no act, and its paths end as those of the run
`s` of the set monad. -/
structure TRun.NoActs (R : TRun A O) (s : Run O) : Prop where
  ok_acts : ∀ x mt, R (.ok (x, mt)) → Step.actsOf mt = []
  error_acts : ∀ r mt, R (.error (r, mt)) → Step.actsOf mt = []
  ok_iff : ∀ x, (∃ mt, R (.ok (x, mt))) ↔ s (.ok x)
  error_iff : ∀ r, (∃ mt, R (.error (r, mt))) ↔ s (.ub r)

/-- The traced observable behaviour of a run that shows no act is the
observable behaviour of the run of the set monad whose paths it ends as,
each outcome with an empty trace. -/
theorem traceObservable_of_noActs {run : Nat → TRun A O} {s : Nat → Run O}
    (h : ∀ n, (run n).NoActs (s n)) : traceObservable run = .ofBehaviour (observable s) := by
  funext t
  apply propext
  cases t with
  | ret tr o =>
    constructor
    · rintro ⟨n, mt, hr, rfl⟩
      rw [(h n).ok_acts _ _ hr]
      exact ⟨.ret o, ⟨n, (h n).ok_iff _ |>.1 ⟨mt, hr⟩⟩, rfl⟩
    · rintro ⟨o' | _ | _, ho, he⟩ <;> cases he
      obtain ⟨n, hs⟩ := ho
      obtain ⟨mt, hr⟩ := (h n).ok_iff _ |>.2 hs
      exact ⟨n, mt, hr, (h n).ok_acts _ _ hr⟩
  | ub tr r =>
    constructor
    · rintro ⟨n, mt, hr, rfl⟩
      rw [(h n).error_acts _ _ hr]
      exact ⟨.ub r, ⟨n, (h n).error_iff _ |>.1 ⟨mt, hr⟩⟩, rfl⟩
    · rintro ⟨_ | r' | _, ho, he⟩ <;> cases he
      obtain ⟨n, hs⟩ := ho
      obtain ⟨mt, hr⟩ := (h n).error_iff _ |>.2 hs
      exact ⟨n, mt, hr, (h n).error_acts _ _ hr⟩
  | diverge tr =>
    constructor
    · rintro ⟨N, hN⟩
      obtain ⟨mt, hr, _, he⟩ := hN N
      have h0 := Step.actsOf_upTo_eq_nil ((h N).ok_acts _ _ hr) N
      rw [he (Nat.le_refl N)] at h0
      subst h0
      exact ⟨.fuelExhausted, fun n => (h n).ok_iff _ |>.1 ((hN n).elim fun mt h => ⟨mt, h.1⟩), rfl⟩
    · rintro ⟨_ | _ | _, ho, he⟩ <;> cases he
      refine ⟨0, fun n => ?_⟩
      obtain ⟨mt, hr⟩ := (h n).ok_iff _ |>.2 (ho n)
      have h0 := (h n).ok_acts _ _ hr
      exact ⟨mt, hr, h0 ▸ List.prefix_refl [], fun _ => Step.actsOf_upTo_eq_nil h0 0⟩
  | reacts T =>
    constructor
    · rintro ⟨K, hK⟩
      obtain ⟨mt, hr, _, hk⟩ := hK (K 1)
      have h0 := Step.actsOf_upTo_eq_nil ((h _).ok_acts _ _ hr) (K 1)
      have := hk 1 (Nat.le_refl _)
      rw [h0] at this
      simp at this
    · rintro ⟨_ | _ | _, _, he⟩ <;> cases he

/-! # The traced runs of functions -/

/-- The traced runs of a function: for each argument vector, its traced run
at each budget. -/
def FuncTraceRuns (Args A O : Type) : Type := Args → Nat → TRun A O

namespace FuncTraceRuns

variable {Args : Type} [HRefinement A A] [HRefinement O O]

/-- The target function refines the source function: on every argument
vector, its traced observable behaviour refines the source's. -/
def IsRefinedBy (src tgt : FuncTraceRuns Args A O) : Prop :=
  ∀ a, traceObservable (src a) ⊑ traceObservable (tgt a)

instance : HRefinement (FuncTraceRuns Args A O) (FuncTraceRuns Args A O) := ⟨IsRefinedBy⟩

/-- Refinement of traced functions is reflexive when refinement of acts and
of observations is. -/
theorem isRefinedBy_refl (hA : ∀ a : A, a ⊑ a) (hO : ∀ o : O, o ⊑ o)
    (f : FuncTraceRuns Args A O) : f ⊑ f :=
  fun a => TBehaviour.isRefinedBy_refl hA hO (traceObservable (f a))

/-- Refinement of traced functions is transitive when refinement of acts and
of observations is. -/
theorem isRefinedBy_trans (hA : ∀ {a b c : A}, a ⊑ b → b ⊑ c → a ⊑ c)
    (hO : ∀ {a b c : O}, a ⊑ b → b ⊑ c → a ⊑ c) {f g h : FuncTraceRuns Args A O}
    (hfg : f ⊑ g) (hgh : g ⊑ h) : f ⊑ h :=
  fun a => TBehaviour.isRefinedBy_trans hA hO (hfg a) (hgh a)

/-- Traced functions that show no act refine exactly when the functions whose
runs they end as refine. -/
theorem isRefinedBy_iff_of_noActs {src tgt : FuncTraceRuns Args A O} {F G : FuncRuns Args O}
    (hs : ∀ a n, (src a n).NoActs (F a n)) (ht : ∀ a n, (tgt a n).NoActs (G a n)) :
    src ⊑ tgt ↔ F ⊑ G := by
  show (∀ a, _) ↔ ∀ a, _
  refine forall_congr' fun a => ?_
  rw [traceObservable_of_noActs (hs a), traceObservable_of_noActs (ht a)]
  exact TBehaviour.ofBehaviour_isRefinedBy_iff

end FuncTraceRuns

/-- Refinement of traced functions holds for every world: on every argument
vector, at every world, each outcome that the target shows there is allowed
by an outcome of the source, which shows the same answers. -/
theorem FuncTraceRuns.isRefinedBy_iff_world {Args E Ans : Type} [HRefinement E E]
    [HRefinement O O] [Inhabited Ans] {src tgt : FuncTraceRuns Args (Act E Ans) O} :
    src ⊑ tgt ↔ ∀ a w t, (traceObservable (tgt a)).atWorld w t →
      ∃ s, traceObservable (src a) s ∧ s ⊑ t :=
  forall_congr' fun _ => TBehaviour.isRefinedBy_iff_world

end Fir
