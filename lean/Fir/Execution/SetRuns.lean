import Fir.Execution.Behaviour

/-!
# Reading a run path by path

The proofs of the next sections read a run in the set monad path by path.
A computation of `ExceptT Stuck SetM` is the set of the ways its paths
end: with a result, stuck, or with UB. The lemmas below say how each
building block of the interpreter ends. A path of `x >>= g` either goes
through a result `a` of `x` and ends as a path of `g a` ends, or ends where
`x` is stuck or hits UB.

Two properties of a computation follow its binds: that no path is stuck
(`NoStuck`), and that it has a path at all (`HasPath`).
-/

namespace Fir.SetM

variable {ε α β : Type}

/-- `pure a` ends with `a`, and only so. -/
theorem run_pure (a : α) (e : Ev (Except ε α)) :
    (pure a : ExceptT ε SetM α).run e ↔ e = .ok (.ok a) :=
  Iff.rfl

/-- A path of `x >>= g` goes through a result of `x`, or ends where `x`
ends with an error or with UB. -/
theorem run_bind (x : ExceptT ε SetM α) (g : α → ExceptT ε SetM β) (e : Ev (Except ε β)) :
    (x >>= g).run e ↔ (∃ a, x.run (.ok (.ok a)) ∧ (g a).run e) ∨
      (∃ er, x.run (.ok (.error er)) ∧ e = .ok (.error er)) ∨
      (∃ r, x.run (.ub r) ∧ e = .ub r) := by
  show ((∃ a, x.run (.ok a) ∧ ExceptT.bindCont g a e) ∨ ∃ r, x.run (.ub r) ∧ e = .ub r) ↔ _
  constructor
  · rintro (⟨er | a, hx, h⟩ | h)
    · exact .inr (.inl ⟨er, hx, h⟩)
    · exact .inl ⟨a, hx, h⟩
    · exact .inr (.inr h)
  · rintro (⟨a, hx, h⟩ | ⟨er, hx, rfl⟩ | h)
    · exact .inl ⟨.ok a, hx, h⟩
    · exact .inl ⟨.error er, hx, rfl⟩
    · exact .inr h

/-- `liftExcept x` ends with `x`, and only so. -/
theorem run_liftExcept (x : Except ε α) (e : Ev (Except ε α)) :
    (liftExcept x : ExceptT ε SetM α).run e ↔ e = .ok x := by
  cases x <;> exact Iff.rfl

/-- A computation of the set monad, lifted, ends as it ends. -/
theorem run_lift (s : SetM α) (e : Ev (Except ε α)) :
    (ExceptT.lift s : ExceptT ε SetM α).run e ↔
      (∃ a, s (.ok a) ∧ e = .ok (.ok a)) ∨ (∃ r, s (.ub r) ∧ e = .ub r) :=
  Iff.rfl

end Fir.SetM

namespace Fir

open SetM

/-! # Two properties of a computation -/

/-- No path of `s` is stuck. -/
def NoStuck (s : ExceptT Stuck SetM α) : Prop := ∀ st, ¬ s.run (.ok (.error st))

/-- `s` has a path: it ends in some way. -/
def HasPath (s : ExceptT Stuck SetM α) : Prop := ∃ e, s.run e

namespace NoStuck

theorem pure' {a : α} : NoStuck (pure a : ExceptT Stuck SetM α) :=
  fun _ h => nomatch (run_pure _ _).1 h

theorem liftExcept_ok {a : α} :
    NoStuck (liftExcept (Except.ok a : Except Stuck α) : ExceptT Stuck SetM α) :=
  fun _ h => nomatch (run_liftExcept _ _).1 h

theorem lift {s : SetM α} : NoStuck (ExceptT.lift s : ExceptT Stuck SetM α) := fun _ h => by
  rcases (run_lift _ _).1 h with ⟨_, _, he⟩ | ⟨_, _, he⟩ <;> cases he

theorem bind {x : ExceptT Stuck SetM α} {g : α → ExceptT Stuck SetM β} (hx : NoStuck x)
    (hg : ∀ a, x.run (.ok (.ok a)) → NoStuck (g a)) : NoStuck (x >>= g) := fun st h => by
  rcases (run_bind x g _).1 h with ⟨a, ha, h⟩ | ⟨st', hst, _⟩ | ⟨_, _, he⟩
  · exact hg a ha st h
  · exact hx st' hst
  · cases he

end NoStuck

namespace HasPath

theorem pure' {a : α} : HasPath (pure a : ExceptT Stuck SetM α) := ⟨_, rfl⟩

theorem bind_ok {x : ExceptT Stuck SetM α} {g : α → ExceptT Stuck SetM β} {a : α}
    (hx : x.run (.ok (.ok a))) (hg : HasPath (g a)) : HasPath (x >>= g) :=
  let ⟨e, he⟩ := hg
  ⟨e, (run_bind x g e).2 (.inl ⟨a, hx, he⟩)⟩

theorem bind_lift {s : SetM α} {g : α → ExceptT Stuck SetM β} (hs : ∃ e, s e)
    (hg : ∀ a, s (.ok a) → HasPath (g a)) : HasPath (ExceptT.lift s >>= g) := by
  obtain ⟨e, he⟩ := hs
  cases e with
  | ok a => exact bind_ok ((run_lift _ _).2 (.inl ⟨a, he, rfl⟩)) (hg a he)
  | ub r =>
    exact ⟨.ub r, (run_bind _ g _).2 (.inr (.inr ⟨r, (run_lift _ _).2 (.inr ⟨r, he, rfl⟩), rfl⟩))⟩

end HasPath

end Fir
