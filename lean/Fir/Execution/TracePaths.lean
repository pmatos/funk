import Fir.Execution.TraceObligations

/-!
# Paths of the interpreter in the traced layer

The interpreter runs a function's ops in a monad that may also end stuck,
over the monad of the run's effects. Over the traced layer, a path of such a
computation, from a traced state, ends with a value, stuck, or in UB, each
with the acts it showed, and with the traced state it ends in unless it hits
UB. This section says how the interpreter's building blocks end there:

* a sequence ends as its first computation, when that ends stuck or in UB,
  or goes on by its second from the value and the traced state that the
  first ends with, after the acts the first showed;
* `pure` and a check end at once, showing nothing; a check that fails is
  stuck;
* a computation of the traced layer that the interpreter runs ends as it
  does, and is never stuck.
-/

namespace Fir

variable {B σ α β ε : Type}

/-! # Paths of the interpreter's computations in the traced layer -/

/-- A way a computation of the interpreter ends in the traced layer that is
not stuck. -/
def TraceEnd.NotStuck (e : TraceEnd B σ (Except ε α)) : Prop :=
  ∀ er t s, e ≠ .ok (.error er, t, s)

/-- A way of ending that is not stuck after a trace is not stuck before it. -/
theorem TraceEnd.NotStuck.of_after {t : List B} {e : TraceEnd B σ (Except ε α)}
    (h : TraceEnd.NotStuck (e.after t)) : TraceEnd.NotStuck e := by
  rintro er t' s rfl
  exact h er (t ++ t') s rfl

/-- UB is not stuck. -/
theorem TraceEnd.notStuck_error (r : String) (t : List B) :
    TraceEnd.NotStuck (Except.error (r, t) : TraceEnd B σ (Except ε α)) :=
  fun _ _ _ h => nomatch h

/-- A result is not stuck. -/
theorem TraceEnd.notStuck_ok (a : α) (t : List B) (s : σ) :
    TraceEnd.NotStuck (Except.ok (Except.ok a, t, s) : TraceEnd B σ (Except ε α)) :=
  fun _ _ _ h => by cases h

/-- A way of ending that is not stuck is not stuck after a trace. -/
theorem TraceEnd.NotStuck.after {t : List B} {e : TraceEnd B σ (Except ε α)}
    (h : TraceEnd.NotStuck e) : TraceEnd.NotStuck (e.after t) := by
  rcases e with ⟨_, _⟩ | ⟨y, t', s⟩
  · exact TraceEnd.notStuck_error _ _
  · rcases y with er | a
    · exact absurd rfl (h er t' s)
    · exact TraceEnd.notStuck_ok _ _ _

/-- A way of ending that allows another is not stuck, when the relation on
what they give relates no stuck path to anything. -/
theorem TraceEnd.Allows.notStuck [HRefinement B B] [HRefinement σ σ] {γ : Type}
    {r : Except ε α → γ → Prop} (hr : ∀ er b, ¬ r (.error er) b) :
    ∀ {e : TraceEnd B σ (Except ε α)} {e' : TraceEnd B σ γ}, TraceEnd.Allows r e e' →
      TraceEnd.NotStuck e
  | .error _, _, _ => TraceEnd.notStuck_error _ _
  | .ok (.ok _, _, _), _, _ => TraceEnd.notStuck_ok _ _ _
  | .ok (.error _, _, _), .ok (_, _, _), h => (hr _ _ h.1).elim
  | .ok (.error _, _, _), .error _, h => h.elim

namespace TraceM

/-- The ways a sequence of the interpreter ends in the traced layer: each way
its first computation ends with a value, followed by a way its second ends,
after the first's trace; each way its first ends stuck; and each way its
first ends in UB. -/
theorem run_except_bind (x : ExceptT ε (TraceM B σ) α) (f : α → ExceptT ε (TraceM B σ) β)
    (s : σ) (e : TraceEnd B σ (Except ε β)) :
    (x >>= f).run s e ↔
      (∃ a t s' e', x.run s (.ok (.ok a, t, s')) ∧ (f a).run s' e' ∧ e = e'.after t) ∨
      (∃ er t s', x.run s (.ok (.error er, t, s')) ∧ e = .ok (.error er, t, s')) ∨
      (∃ r t, x.run s (.error (r, t)) ∧ e = .error (r, t)) := by
  show (x.run >>= ExceptT.bindCont f) s e ↔ _
  rw [TraceM.bind_apply]
  constructor
  · rintro (⟨r, t, s', e', hx, hf, rfl⟩ | ⟨r, t, hx, rfl⟩)
    · cases r with
      | ok a => exact .inl ⟨a, t, s', e', hx, hf, rfl⟩
      | error er =>
        have hf : e' = .ok (.error er, [], s') := hf
        subst hf
        exact .inr (.inl ⟨er, t, s', hx, by simp [TraceEnd.after]⟩)
    · exact .inr (.inr ⟨r, t, hx, rfl⟩)
  · rintro (⟨a, t, s', e', hx, hf, rfl⟩ | ⟨er, t, s', hx, rfl⟩ | ⟨r, t, hx, rfl⟩)
    · exact .inl ⟨.ok a, t, s', e', hx, hf, rfl⟩
    · exact .inl ⟨.error er, t, s', _, hx, rfl, by simp [TraceEnd.after]⟩
    · exact .inr ⟨r, t, hx, rfl⟩

/-- `pure` ends with its value, showing nothing. -/
theorem run_except_pure (a : α) (s : σ) (e : TraceEnd B σ (Except ε α)) :
    (pure a : ExceptT ε (TraceM B σ) α).run s e ↔ e = .ok (.ok a, [], s) :=
  Iff.rfl

/-- A check ends as it says, showing nothing. -/
theorem run_liftExcept (x : Except ε α) (s : σ) (e : TraceEnd B σ (Except ε α)) :
    (liftExcept x : ExceptT ε (TraceM B σ) α).run s e ↔ e = .ok (x, [], s) := by
  cases x <;> exact Iff.rfl

/-- A computation of the traced layer, run by the interpreter, ends as it
does, and is never stuck. -/
theorem run_lift (c : TraceM B σ α) (s : σ) (e : TraceEnd B σ (Except ε α)) :
    (ExceptT.lift c : ExceptT ε (TraceM B σ) α).run s e ↔
      (∃ a t s', c s (.ok (a, t, s')) ∧ e = .ok (.ok a, t, s')) ∨
      (∃ r t, c s (.error (r, t)) ∧ e = .error (r, t)) := by
  show (Except.ok <$> c) s e ↔ _
  rw [map_eq_pure_bind, TraceM.bind_apply]
  constructor
  · rintro (⟨a, t, s', e', hc, he', rfl⟩ | ⟨r, t, hc, rfl⟩)
    · have he' : e' = .ok (.ok a, [], s') := he'
      subst he'
      exact .inl ⟨a, t, s', hc, by simp [TraceEnd.after]⟩
    · exact .inr ⟨r, t, hc, rfl⟩
  · rintro (⟨a, t, s', hc, rfl⟩ | ⟨r, t, hc, rfl⟩)
    · exact .inl ⟨a, t, s', _, hc, rfl, by simp [TraceEnd.after]⟩
    · exact .inr ⟨r, t, hc, rfl⟩

/-- A path of a computation of the traced layer, then `g`, goes on from one of
its results with the traced state it ends with, after its acts, or ends
where it hits UB. -/
theorem run_lift_bind (c : TraceM B σ β) (g : β → ExceptT ε (TraceM B σ) α) (s : σ)
    (e : TraceEnd B σ (Except ε α)) :
    (ExceptT.lift c >>= g).run s e ↔
      (∃ b t s' e', c s (.ok (b, t, s')) ∧ (g b).run s' e' ∧ e = e'.after t) ∨
      (∃ r t, c s (.error (r, t)) ∧ e = .error (r, t)) := by
  rw [run_except_bind]
  constructor
  · rintro (⟨b, t, s', e', hx, hg, rfl⟩ | ⟨er, t, s', hx, rfl⟩ | ⟨r, t, hx, rfl⟩)
    · rcases (run_lift c s _).1 hx with ⟨_, _, _, hc, he⟩ | ⟨_, _, _, he⟩ <;> cases he
      exact .inl ⟨b, t, s', e', hc, hg, rfl⟩
    · rcases (run_lift c s _).1 hx with ⟨_, _, _, _, he⟩ | ⟨_, _, _, he⟩ <;> cases he
    · rcases (run_lift c s _).1 hx with ⟨_, _, _, _, he⟩ | ⟨_, _, hc, he⟩ <;> cases he
      exact .inr ⟨r, t, hc, rfl⟩
  · rintro (⟨b, t, s', e', hc, hg, rfl⟩ | ⟨r, t, hc, rfl⟩)
    · exact .inl ⟨b, t, s', e', (run_lift c s _).2 (.inl ⟨b, t, s', hc, rfl⟩), hg, rfl⟩
    · exact .inr (.inr ⟨r, t, (run_lift c s _).2 (.inr ⟨r, t, hc, rfl⟩), rfl⟩)

/-- A path of a check, then `g`, that is not stuck goes on from the value
that the check holds, from the same traced state. -/
theorem run_liftExcept_bind {x : Except ε β} {g : β → ExceptT ε (TraceM B σ) α} {s : σ}
    {e : TraceEnd B σ (Except ε α)} (hne : TraceEnd.NotStuck e) :
    (liftExcept x >>= g).run s e ↔ ∃ b, x = .ok b ∧ (g b).run s e := by
  rw [run_except_bind]
  constructor
  · rintro (⟨b, t, s', e', hx, hg, rfl⟩ | ⟨er, t, s', hx, rfl⟩ | ⟨r, t, hx, rfl⟩)
    · have hx := (run_liftExcept x s _).1 hx
      cases x with
      | error _ => cases hx
      | ok b' =>
        injection hx with hx
        injection hx with h₁ h₂
        injection h₁ with h₁
        injection h₂ with h₂ h₃
        subst h₁ h₂ h₃
        exact ⟨b, rfl, by simpa using hg⟩
    · exact absurd rfl (hne er t s')
    · cases (run_liftExcept x s _).1 hx
  · rintro ⟨b, rfl, h⟩
    exact .inl ⟨b, [], s, e, rfl, h, by simp⟩

/-- A check that fails is stuck, showing nothing. -/
theorem run_stuck {st : Stuck} {s : σ} {e : TraceEnd B σ (Except Stuck α)} (hne : TraceEnd.NotStuck e) :
    ¬ (liftExcept (.error st) : ExceptT Stuck (TraceM B σ) α).run s e := fun h =>
  hne st [] s ((run_liftExcept _ s e).1 h)

end TraceM


end Fir
