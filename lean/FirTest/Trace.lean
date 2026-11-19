import Fir

/-!
Tests of traces and worlds with a toy event (ADR-2026-11-09-1540). The core
dialect shows no event yet: the tickets that bring external calls, volatile
accesses and inline assembly add its events. The toy event here holds a
value, poison or a number, and the world answers it with a number. Each test
builds a traced run, from a computation of the traced layer or one budget at
a time with its marked traces, and checks what its traced behaviour holds
and which runs refine which:

* UB keeps the trace before it, and UB in the source allows only a target
  that first shows the source's events;
* a loop that falls silent, a loop that shows an event at every step, and a
  loop that shows one event and then falls silent: none of them refines
  another, and the loop that shows events forever has a behaviour;
* a loop that may stop at any step, show an event and return does not fall
  silent after the event, and a loop that may count up to any number and
  then show that many events does not show events forever. At each budget
  both can run out of fuel after the same acts as a run that does, but not
  within a bounded number of steps;
* poison in an event is refined by any value, and the world's answer to the
  target's event is an answer to the source's.
-/

namespace FirTest.Trace

open Fir

/-- An act of the toy event: a value shown to the world, and its answer. -/
abbrev A := Act (PoisonOr Nat) Nat

/-- What a toy run returns. -/
abbrev O := PoisonOr Nat

/-- The traced layer of the tests, with no memory. -/
abbrev T := TraceM A Unit

/-- The traced run, at every budget, of a computation of the layer that
returns: it marks no step. -/
def runOf (x : T O) : Nat → TRun A O :=
  fun _ e => ∃ e', x () e' ∧
    e = (e'.mapActs fun a => [Step.act a]).map fun p => (.ok (.ret p.1), p.2.1)

/-- The acts of a trace with no step are the trace. -/
theorem actsOf_map_act (t : List A) : Step.actsOf (t.flatMap fun a => [Step.act a]) = t := by
  induction t with
  | nil => rfl
  | cons a t ih => simpa [Step.actsOf, Step.acts] using ih

/-- The traced behaviour of a computation that returns: its returns and its
UB, each with its trace. -/
theorem traceObservable_runOf (x : T O) (t : TOutcome A O) :
    traceObservable (runOf x) t ↔ (∃ tr o, t = .ret tr o ∧ x () (.ok (o, tr, ()))) ∨
      ∃ tr r, t = .ub tr r ∧ x () (.error (r, tr)) := by
  cases t with
  | ret tr o =>
    constructor
    · rintro ⟨_, _, ⟨(⟨_, _⟩ | ⟨_, _, ⟨⟩⟩), h, he⟩, rfl⟩ <;> cases he
      exact .inl ⟨_, _, by rw [actsOf_map_act], h⟩
    · rintro (⟨_, _, he, h⟩ | ⟨_, _, he, _⟩) <;> cases he
      exact ⟨0, _, ⟨_, h, rfl⟩, actsOf_map_act _⟩
  | ub tr r =>
    constructor
    · rintro ⟨_, _, ⟨(⟨_, _⟩ | ⟨_, _, ⟨⟩⟩), h, he⟩, rfl⟩ <;> cases he
      exact .inr ⟨_, _, by rw [actsOf_map_act], h⟩
    · rintro (⟨_, _, he, _⟩ | ⟨_, _, he, h⟩) <;> cases he
      exact ⟨0, _, ⟨_, h, rfl⟩, actsOf_map_act _⟩
  | diverge tr =>
    constructor
    · rintro ⟨N, h⟩
      obtain ⟨_, ⟨(⟨_, _⟩ | ⟨_, _, ⟨⟩⟩), _, he⟩, _⟩ := h N <;> cases he
    · rintro (⟨_, _, he, _⟩ | ⟨_, _, he, _⟩) <;> cases he
  | reacts T =>
    constructor
    · rintro ⟨K, hK⟩
      obtain ⟨_, ⟨(⟨_, _⟩ | ⟨_, _, ⟨⟩⟩), _, he⟩, _⟩ := hK 0 <;> cases he
    · rintro (⟨_, _, he, _⟩ | ⟨_, _, he, _⟩) <;> cases he

/-! # UB keeps the trace before it -/

/-- Show `x` to the world, then hit UB. -/
def emitThenUB (x : PoisonOr Nat) : T O := do
  let _ ← MonadEvent.emit x
  MonadUB.ub "r"

/-- Show `x` to the world, then return its answer. -/
def emitRet (x : PoisonOr Nat) : T O := do
  let a ← MonadEvent.emit x
  pure (.value a)

/-- Return 0, showing nothing. -/
def ret0 : T O := pure (.value 0)

/-- UB after an event ends the path after that event, whatever the answer. -/
theorem emitThenUB_iff (x : PoisonOr Nat) (e : TraceEnd A Unit O) :
    emitThenUB x () e ↔ ∃ a, e = .error ("r", [⟨x, a⟩]) := by
  rw [emitThenUB, TraceM.bind_apply]
  constructor
  · rintro (⟨a, _, _, _, ⟨_, he⟩, rfl, rfl⟩ | ⟨_, _, ⟨_, he⟩, rfl⟩) <;> cases he
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact .inl ⟨a, _, (), _, ⟨a, rfl⟩, rfl, rfl⟩

/-- An event then a return returns the answer, after the event. -/
theorem emitRet_iff (x : PoisonOr Nat) (e : TraceEnd A Unit O) :
    emitRet x () e ↔ ∃ a, e = .ok (.value a, [⟨x, a⟩], ()) := by
  rw [emitRet, TraceM.bind_apply]
  constructor
  · rintro (⟨a, _, _, _, ⟨_, he⟩, rfl, rfl⟩ | ⟨_, _, ⟨_, he⟩, rfl⟩) <;> cases he
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact .inl ⟨a, _, (), _, ⟨a, rfl⟩, rfl, rfl⟩

/-- A return with nothing shown. -/
theorem ret0_iff (e : TraceEnd A Unit O) : ret0 () e ↔ e = .ok (.value 0, [], ()) :=
  Iff.rfl

/-- UB after an event allows a target that shows the event and returns. -/
theorem emitThenUB_isRefinedBy_emitRet :
    traceObservable (runOf (emitThenUB (.value 5))) ⊑ traceObservable (runOf (emitRet (.value 5))) := by
  intro t ht
  rcases (traceObservable_runOf _ t).1 ht with ⟨tr, o, rfl, h⟩ | ⟨tr, r, rfl, h⟩
  · obtain ⟨a, he⟩ := (emitRet_iff _ _).1 h
    cases he
    exact ⟨.ub [⟨.value 5, a⟩] "r", (traceObservable_runOf _ _).2
      (.inr ⟨_, _, rfl, (emitThenUB_iff _ _).2 ⟨a, rfl⟩⟩),
      fun i b hb => ⟨b, hb, PoisonOr.isRefinedBy_refl _, rfl⟩⟩
  · obtain ⟨a, he⟩ := (emitRet_iff _ _).1 h
    cases he

/-- UB after an event does not allow a target that returns without showing
it. -/
theorem emitThenUB_not_isRefinedBy_ret0 :
    ¬ traceObservable (runOf (emitThenUB (.value 5))) ⊑ traceObservable (runOf ret0) := by
  intro h
  obtain ⟨s, hs, hst⟩ := h (.ret [] (.value 0)) ((traceObservable_runOf _ _).2
    (.inl ⟨_, _, rfl, (ret0_iff _).2 rfl⟩))
  rcases (traceObservable_runOf _ s).1 hs with ⟨_, _, rfl, h⟩ | ⟨_, _, rfl, h⟩
  · obtain ⟨_, he⟩ := (emitThenUB_iff _ _).1 h
    cases he
  · obtain ⟨a, he⟩ := (emitThenUB_iff _ _).1 h
    cases he
    obtain ⟨_, hb, _⟩ := hst 0 ⟨.value 5, a⟩ rfl
    cases hb

/-- UB before any event allows every target. -/
theorem ubFirst_isRefinedBy (tgt : TBehaviour A O) :
    traceObservable (runOf (MonadUB.ub "r")) ⊑ tgt :=
  TBehaviour.ub_isRefinedBy ((traceObservable_runOf _ _).2 (.inr ⟨_, _, rfl, rfl⟩)) tgt

/-! # Marked traces of loops -/

/-- The act of the loops below. -/
def act₁ : A := ⟨.value 1, 0⟩

/-- A step of the run. -/
abbrev tick : Step A := .tick

/-- Steps show no act. -/
theorem actsOf_ticks (n : Nat) : Step.actsOf (List.replicate n tick) = [] := by
  simp [Step.actsOf, Step.acts]

/-- What a marked trace that starts with more than `N` steps shows in its
first `N` steps is `N` steps. -/
theorem upTo_ticks_append : ∀ (N m : Nat) (rest : List (Step A)), N < m →
    Step.upTo N (List.replicate m tick ++ rest) = List.replicate N tick
  | 0, m + 1, _, _ => rfl
  | N + 1, m + 1, rest, h => by
    simp only [List.replicate_succ, List.cons_append, Step.upTo]
    rw [upTo_ticks_append N m rest (by omega)]

/-- `n` steps, each showing `act₁`. -/
def emits (n : Nat) : List (Step A) := (List.replicate n [tick, .act act₁]).flatten

/-- `n` steps that each show `act₁` show `n` of them. -/
theorem actsOf_emits (n : Nat) : Step.actsOf (emits n) = List.replicate n act₁ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [emits, List.replicate_succ, List.flatten_cons] at ih ⊢
    simpa [Step.actsOf, Step.acts] using ih

/-- In their first `k` steps, `n` steps that each show `act₁` show as many
of them as they have steps there. -/
theorem actsOf_upTo_emits : ∀ (k n : Nat),
    Step.actsOf (Step.upTo k (emits n)) = List.replicate (min k n) act₁
  | 0, 0 => rfl
  | 0, n + 1 => rfl
  | k + 1, 0 => rfl
  | k + 1, n + 1 => by
    have := actsOf_upTo_emits k n
    simp only [emits, List.replicate_succ, List.flatten_cons] at this ⊢
    simp only [List.cons_append, List.nil_append, Step.upTo]
    simp only [Step.actsOf, List.flatMap_cons, Step.acts] at this ⊢
    rw [this, Nat.add_min_add_right]
    simp [List.replicate_succ]

/-! # Divergence -/

/-- A loop that falls silent at once: one step at each budget. -/
def silent : Nat → TRun A O := fun n e => e = .ok (.ok .fuelExhausted, List.replicate n tick)

/-- A loop that shows `act₁` at every step. -/
def emitter : Nat → TRun A O := fun n e => e = .ok (.ok .fuelExhausted, emits n)

/-- A loop that shows `act₁` at its first step, then falls silent. -/
def once : Nat → TRun A O :=
  fun n e => e = .ok (.ok .fuelExhausted, if n = 0 then [] else emits 1 ++ List.replicate (n - 1) tick)

/-- A silent loop diverges with an empty trace, and only so. -/
theorem silent_iff (t : TOutcome A O) : traceObservable silent t ↔ t = .diverge [] := by
  cases t with
  | ret | ub =>
    constructor
    · rintro ⟨_, _, ⟨⟩, _⟩
    · rintro ⟨⟩
  | diverge tr =>
    constructor
    · rintro ⟨N, h⟩
      obtain ⟨_, he, _, hN⟩ := h N
      cases he
      rw [← hN (Nat.le_refl N), Step.actsOf_upTo_eq_nil (actsOf_ticks N)]
    · rintro ⟨⟩
      exact ⟨0, fun n => ⟨_, rfl, by rw [actsOf_ticks]; exact List.prefix_refl [],
        fun _ => Step.actsOf_upTo_eq_nil (actsOf_ticks n) 0⟩⟩
  | reacts T =>
    constructor
    · rintro ⟨K, hK⟩
      obtain ⟨_, he, _, hk⟩ := hK (K 1)
      cases he
      have := hk 1 (Nat.le_refl _)
      rw [Step.actsOf_upTo_eq_nil (actsOf_ticks _)] at this
      simp at this
    · rintro ⟨⟩

/-- The loop that shows `act₁` at every step shows its infinite trace: it has
a behaviour. -/
theorem emitter_reacts : traceObservable emitter (.reacts fun _ => act₁) :=
  ⟨fun k => k, fun n => ⟨_, rfl, fun i a ha => by
    rw [actsOf_emits, List.getElem?_replicate] at ha
    split at ha <;> cases ha
    rfl, fun k hk => by simp [actsOf_upTo_emits, Nat.min_eq_left hk]⟩⟩

/-- The loop that shows `act₁` at every step never falls silent, returns or
hits UB. -/
theorem emitter_reacts_only {t : TOutcome A O} (h : traceObservable emitter t) :
    ∃ T, t = .reacts T := by
  cases t with
  | ret | ub => obtain ⟨_, _, ⟨⟩, _⟩ := h
  | diverge tr =>
    obtain ⟨_, hN⟩ := h
    obtain ⟨_, he, hp, _⟩ := hN (tr.length + 1)
    cases he
    have := hp.length_le
    rw [actsOf_emits, List.length_replicate] at this
    omega
  | reacts T => exact ⟨T, rfl⟩

/-- The loop that shows `act₁` once falls silent after it. -/
theorem once_diverge : traceObservable once (.diverge [act₁]) := by
  refine ⟨1, fun n => ⟨_, rfl, ?_, fun hn => ?_⟩⟩
  · by_cases h : n = 0
    · simp [h, Step.actsOf]
    · simp [h, emits, Step.actsOf, Step.acts, act₁]
  · have h0 : Step.upTo 0 (List.replicate (n - 1) tick) = [] := by cases n - 1 <;> rfl
    simp only [show n ≠ 0 by omega, ite_false, emits, List.replicate_one, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, Step.upTo, h0]
    rfl

/-- A loop that shows events forever does not refine a silent loop. -/
theorem silent_not_isRefinedBy_emitter : ¬ traceObservable silent ⊑ traceObservable emitter := by
  intro h
  obtain ⟨s, hs, hst⟩ := h _ emitter_reacts
  cases (silent_iff s).1 hs
  exact hst

/-- A silent loop does not refine a loop that shows events forever. -/
theorem emitter_not_isRefinedBy_silent : ¬ traceObservable emitter ⊑ traceObservable silent := by
  intro h
  obtain ⟨s, hs, hst⟩ := h _ ((silent_iff _).2 rfl)
  obtain ⟨_, rfl⟩ := emitter_reacts_only hs
  exact hst

/-- A loop that shows one event, then falls silent, does not refine a silent
loop. -/
theorem silent_not_isRefinedBy_once : ¬ traceObservable silent ⊑ traceObservable once := by
  intro h
  obtain ⟨s, hs, hst⟩ := h _ once_diverge
  cases (silent_iff s).1 hs
  exact hst

/-- A loop that shows one event, then falls silent, does not refine a loop
that shows events forever. -/
theorem emitter_not_isRefinedBy_once : ¬ traceObservable emitter ⊑ traceObservable once := by
  intro h
  obtain ⟨s, hs, hst⟩ := h _ once_diverge
  obtain ⟨_, rfl⟩ := emitter_reacts_only hs
  exact hst

/-! # Running out of fuel late is not divergence -/

/-- A loop that may stop at any step, then show `act₁` and return, as it runs
out of fuel at each budget: it is still looping, or it has just shown
`act₁` at its last step. -/
def late : Nat → TRun A O := fun n e =>
  e = .ok (.ok .fuelExhausted, List.replicate n tick) ∨
    e = .ok (.ok .fuelExhausted, List.replicate n tick ++ [.act act₁])

/-- The loop that may stop at any step does not fall silent after `act₁`: it
shows `act₁` only after more and more steps. -/
theorem late_not_diverge : ¬ traceObservable late (.diverge [act₁]) := by
  rintro ⟨N, hN⟩
  obtain ⟨_, he, _, h⟩ := hN (N + 1)
  rcases he with he | he <;> cases he
  · have := h (by omega)
    rw [Step.actsOf_upTo_eq_nil (actsOf_ticks _)] at this
    cases this
  · have := h (by omega)
    rw [upTo_ticks_append N (N + 1) _ (by omega), actsOf_ticks] at this
    cases this

/-- A loop that may count up to any number `m`, and then shows `act₁` at each
of its next `m` steps, as it runs out of fuel at each budget: it is still
counting, or it has shown fewer than `m` of them. -/
def counted : Nat → TRun A O := fun n e =>
  e = .ok (.ok .fuelExhausted, List.replicate n tick) ∨
    ∃ m, m ≤ n ∧ n < 2 * m ∧ e = .ok (.ok .fuelExhausted, List.replicate m tick ++ emits (n - m))

/-- The loop that counts first does not show `act₁` forever: the more acts it
shows, the later the first of them. -/
theorem counted_not_reacts : ¬ traceObservable counted (.reacts fun _ => act₁) := by
  rintro ⟨K, hK⟩
  obtain ⟨_, he, _, hk⟩ := hK (2 * K 1 + 2)
  have h1 := hk 1 (by omega)
  rcases he with he | ⟨m, _, hm, he⟩ <;> cases he
  · rw [Step.actsOf_upTo_eq_nil (actsOf_ticks _)] at h1
    cases h1
  · rw [upTo_ticks_append (K 1) m _ (by omega), actsOf_ticks] at h1
    cases h1

/-! # Poison in an event -/

/-- Showing poison and returning the answer is refined by showing a value and
returning the answer: the world's answer to the value is an answer to the
poison. -/
theorem emitRet_poison_isRefinedBy :
    traceObservable (runOf (emitRet .poison)) ⊑ traceObservable (runOf (emitRet (.value 5))) := by
  intro t ht
  rcases (traceObservable_runOf _ t).1 ht with ⟨tr, o, rfl, h⟩ | ⟨tr, r, rfl, h⟩
  · obtain ⟨a, he⟩ := (emitRet_iff _ _).1 h
    cases he
    exact ⟨.ret [⟨.poison, a⟩] (.value a), (traceObservable_runOf _ _).2
      (.inl ⟨_, _, rfl, (emitRet_iff _ _).2 ⟨a, rfl⟩⟩), ⟨⟨trivial, rfl⟩, trivial⟩, rfl⟩
  · obtain ⟨a, he⟩ := (emitRet_iff _ _).1 h
    cases he

/-- So at every world, each outcome of the target is allowed by an outcome of
the source with the same answers. -/
example (w : World (PoisonOr Nat) Nat) (t : TOutcome A O)
    (ht : (traceObservable (runOf (emitRet (.value 5)))).atWorld w t) :
    ∃ s, traceObservable (runOf (emitRet .poison)) s ∧ s ⊑ t :=
  TBehaviour.isRefinedBy_iff_world.1 emitRet_poison_isRefinedBy w t ht

/-- Showing 5 is not refined by showing 6. -/
theorem emitRet_five_not_isRefinedBy_six :
    ¬ traceObservable (runOf (emitRet (.value 5))) ⊑ traceObservable (runOf (emitRet (.value 6))) := by
  intro h
  obtain ⟨s, hs, hst⟩ := h (.ret [⟨.value 6, 0⟩] (.value 0)) ((traceObservable_runOf _ _).2
    (.inl ⟨_, _, rfl, (emitRet_iff _ _).2 ⟨0, rfl⟩⟩))
  rcases (traceObservable_runOf _ s).1 hs with ⟨_, _, rfl, h⟩ | ⟨_, _, rfl, h⟩
  · obtain ⟨_, he⟩ := (emitRet_iff _ _).1 h
    cases he
    exact nomatch hst.1.1.1
  · obtain ⟨_, he⟩ := (emitRet_iff _ _).1 h
    cases he

end FirTest.Trace
