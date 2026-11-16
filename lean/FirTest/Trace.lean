import Fir

/-!
Tests of traces and worlds with a toy event (ADR-2026-11-09-1540). The core
dialect shows no event yet: the tickets that bring external calls, volatile
accesses and inline assembly add its events. The toy event here holds a
value, poison or a number, and the world answers it with a number. Each test
builds a traced run, from a computation of the traced layer or one budget at
a time, and checks what its traced behaviour holds and which runs refine
which:

* UB keeps the trace before it, and UB in the source allows only a target
  that first shows the source's events;
* a loop that falls silent, a loop that shows an event at every step, and a
  loop that shows one event and then falls silent: none of them refines
  another, and the loop that shows events forever has a behaviour;
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
returns. -/
def runOf (x : T O) : Nat → TRun A O :=
  fun _ e => ∃ e', x ([], ()) e' ∧ e = e'.map fun p => (.ok (.ret p.1), p.2.1)

/-- The traced behaviour of a computation that returns: its returns and its
UB, each with its trace. -/
theorem traceObservable_runOf (x : T O) (t : TOutcome A O) :
    traceObservable (runOf x) t ↔ (∃ tr o, t = .ret tr o ∧ x ([], ()) (.ok (o, (tr, ())))) ∨
      ∃ tr r, t = .ub tr r ∧ x ([], ()) (.error (r, tr)) := by
  cases t with
  | ret tr o =>
    constructor
    · rintro ⟨_, (⟨_, _⟩ | ⟨_, _, ⟨⟩⟩), h, he⟩ <;> cases he
      exact .inl ⟨_, _, rfl, h⟩
    · rintro (⟨_, _, he, h⟩ | ⟨_, _, he, _⟩) <;> cases he
      exact ⟨0, _, h, rfl⟩
  | ub tr r =>
    constructor
    · rintro ⟨_, (⟨_, _⟩ | ⟨_, _, ⟨⟩⟩), h, he⟩ <;> cases he
      exact .inr ⟨_, _, rfl, h⟩
    · rintro (⟨_, _, he, _⟩ | ⟨_, _, he, h⟩) <;> cases he
      exact ⟨0, _, h, rfl⟩
  | diverge tr =>
    constructor
    · rintro ⟨N, h⟩
      obtain ⟨_, ⟨(⟨_, _⟩ | ⟨_, _, ⟨⟩⟩), _, he⟩, _⟩ := h N <;> cases he
    · rintro (⟨_, _, he, _⟩ | ⟨_, _, he, _⟩) <;> cases he
  | reacts T =>
    constructor
    · intro h
      obtain ⟨N, hN⟩ := h 0
      obtain ⟨_, ⟨(⟨_, _⟩ | ⟨_, _, ⟨⟩⟩), _, he⟩, _⟩ := hN N (Nat.le_refl N) <;> cases he
    · rintro (⟨_, _, he, _⟩ | ⟨_, _, he, _⟩) <;> cases he

/-! # UB keeps the trace before it -/

/-- Show `x` to the world, then hit UB. -/
def emitThenUB (x : PoisonOr Nat) : T O := do
  let _ ← MonadEvent.emit (E := PoisonOr Nat) (Ans := Nat) x
  MonadUB.ub "r"

/-- Show `x` to the world, then return its answer. -/
def emitRet (x : PoisonOr Nat) : T O := do
  let a ← MonadEvent.emit (E := PoisonOr Nat) (Ans := Nat) x
  pure (.value a)

/-- Return 0, showing nothing. -/
def ret0 : T O := pure (.value 0)

/-- UB after an event ends the path after that event, whatever the answer. -/
theorem emitThenUB_iff (x : PoisonOr Nat) (e : Except (String × List A) (O × (List A × Unit))) :
    emitThenUB x ([], ()) e ↔ ∃ a, e = .error ("r", [⟨x, a⟩]) := by
  simp [emitThenUB, bind, StateT.bind, ExceptT.bind, ExceptT.bindCont, MonadEvent.emit,
    MonadUB.ub, ExceptT.mk, pure]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, h⟩
    exact ⟨a, h⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, rfl⟩

/-- An event then a return returns the answer, after the event. -/
theorem emitRet_iff (x : PoisonOr Nat) (e : Except (String × List A) (O × (List A × Unit))) :
    emitRet x ([], ()) e ↔ ∃ a, e = .ok (.value a, ([⟨x, a⟩], ())) := by
  simp [emitRet, bind, StateT.bind, ExceptT.bind, ExceptT.bindCont, MonadEvent.emit, ExceptT.mk,
    pure, StateT.pure, ExceptT.pure]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, h⟩
    exact ⟨a, h⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, rfl⟩

/-- A return with nothing shown. -/
theorem ret0_iff (e : Except (String × List A) (O × (List A × Unit))) :
    ret0 ([], ()) e ↔ e = .ok (.value 0, ([], ())) :=
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

/-! # Divergence -/

/-- The act of the loops below. -/
def act₁ : A := ⟨.value 1, 0⟩

/-- A loop that falls silent at once. -/
def silent : Nat → TRun A O := fun _ e => e = .ok (.ok .fuelExhausted, [])

/-- A loop that shows `act₁` at every step. -/
def emitter : Nat → TRun A O := fun n e => e = .ok (.ok .fuelExhausted, List.replicate n act₁)

/-- A loop that shows `act₁` once, then falls silent. -/
def once : Nat → TRun A O := fun n e => e = .ok (.ok .fuelExhausted, if n = 0 then [] else [act₁])

/-- A silent loop diverges with an empty trace, and only so. -/
theorem silent_iff (t : TOutcome A O) : traceObservable silent t ↔ t = .diverge [] := by
  cases t with
  | ret | ub =>
    constructor
    · rintro ⟨_, ⟨⟩⟩
    · rintro ⟨⟩
  | diverge tr =>
    constructor
    · rintro ⟨N, h⟩
      obtain ⟨_, he, _, hN⟩ := h N
      cases he
      rw [← hN (Nat.le_refl N)]
    · rintro ⟨⟩
      exact ⟨0, fun _ => ⟨[], rfl, List.prefix_refl [], fun _ => rfl⟩⟩
  | reacts T =>
    constructor
    · intro h
      obtain ⟨N, hN⟩ := h 1
      obtain ⟨_, he, h0⟩ := hN N (Nat.le_refl N)
      cases he
      exact nomatch h0 0 Nat.one_pos
    · intro h
      cases h

/-- The loop that shows `act₁` forever shows its infinite trace: it has a
behaviour. -/
theorem emitter_reacts : traceObservable emitter (.reacts fun _ => act₁) :=
  fun k => ⟨k, fun n hn => ⟨_, rfl, fun i hi => by
    rw [List.getElem?_replicate]
    simp [show i < n by omega]⟩⟩

/-- The loop that shows `act₁` forever never falls silent, returns or hits
UB. -/
theorem emitter_reacts_only {t : TOutcome A O} (h : traceObservable emitter t) :
    ∃ T, t = .reacts T := by
  cases t with
  | ret | ub => obtain ⟨_, ⟨⟩⟩ := h
  | diverge tr =>
    obtain ⟨N, hN⟩ := h
    obtain ⟨_, he, hp, _⟩ := hN (N + tr.length + 1)
    cases he
    have := hp.length_le
    simp at this
    omega
  | reacts T => exact ⟨T, rfl⟩

/-- The loop that shows `act₁` once falls silent after it. -/
theorem once_diverge : traceObservable once (.diverge [act₁]) :=
  ⟨1, fun n => ⟨_, rfl, by
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn], fun h => by simp [show n ≠ 0 by omega]⟩⟩

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
