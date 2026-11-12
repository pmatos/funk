import Fir.Execution.Values
import Fir.Execution.Effects

/-!
# Outcomes

One run of a function ends in one of three ways. It returns, and an observer
sees what it returned. It hits immediate UB, for a reason. Or it runs out of
fuel.

What an observer sees of a return is the run's _observation_. Each dialect
supplies its observations and how they refine, so that fir can reach any
kind of hardware (ADR-2026-10-29-2016); refinement is not wired to integer
return values. In M0 the observation is the list of returned
values, each a value or poison, since a function may return any number of
values (ADR-2026-10-29-2008). A function that returns one `iN` therefore has
the four outcomes of `fir-ref`: a value, poison, UB with a reason, and fuel
exhausted. The reason that UB carries is for people: refinement ignores it.

This outcome type is M0's. M0 has no I/O, so a run shows nothing to an
observer until it ends. When the external calls that ADR-2026-10-29-2008
foresees arrive, an observer also sees the calls a run makes, and an outcome becomes
a trace of events that ends in a return, UB or divergence. Refinement keeps
its idea, but UB in the source then allows only targets that first show the
source's events before the UB.
-/

namespace Fir

/-- How one run ends, for observations of type `O`. -/
inductive Outcome (O : Type) where
  | ret (o : O)
  | ub (reason : String)
  | fuelExhausted
  deriving Repr, DecidableEq

/-- How a run ends when it neither hits UB nor gets stuck: it returns, or runs
out of fuel. -/
inductive Result (O : Type) where
  | ret (o : O)
  | fuelExhausted
  deriving Repr, DecidableEq

/-!
# Behaviour as a set of outcomes

`freeze` of poison may choose any value, so one function on one input can
run in many ways. Its behaviour is the set of outcomes over all choices
(ADR-2026-10-29-2017). That set is what the interpreter computes when it
reads each computation as a set, the set monad below: a computation is the
set of the ways it may end, with a result or with UB. A choice of bits may
give any bits, and UB ends the computation. `fir-ref`'s exhaustive, scripted
and sampled modes compute this set, or one member of it, and the section on
exhaustive, scripted and sampled modes proves that they do.
-/

/-- One way a computation may end: with a result, or with immediate UB. -/
inductive Ev (α : Type) where
  | ok (a : α)
  | ub (reason : String)
  deriving Repr, DecidableEq

/-- The set monad: a computation is the set of the ways it may end. -/
def SetM (α : Type) : Type := Ev α → Prop

namespace SetM

instance : Monad SetM where
  pure a := fun e => e = .ok a
  bind s f := fun e => (∃ a, s (.ok a) ∧ f a e) ∨ (∃ r, s (.ub r) ∧ e = .ub r)

instance : MonadChoice SetM where
  choose _ := fun e => ∃ b, e = .ok b

instance : MonadUB SetM where
  ub r := fun e => e = .ub r

variable {α β γ : Type}

/-- `pure` then `f` is `f`. -/
theorem pure_bind (a : α) (f : α → SetM β) : (pure a >>= f) = f a := by
  funext e
  apply propext
  show ((∃ a', Ev.ok a' = .ok a ∧ f a' e) ∨ ∃ r, Ev.ub r = .ok a ∧ e = .ub r) ↔ f a e
  constructor
  · rintro (⟨_, h, h'⟩ | ⟨_, h, _⟩)
    · cases h
      exact h'
    · cases h
  · exact fun h => .inl ⟨a, rfl, h⟩

/-- `s` then `pure` is `s`. -/
theorem bind_pure (s : SetM α) : (s >>= pure) = s := by
  funext e
  apply propext
  show ((∃ a, s (.ok a) ∧ e = .ok a) ∨ ∃ r, s (.ub r) ∧ e = .ub r) ↔ s e
  constructor
  · rintro (⟨_, h, rfl⟩ | ⟨_, h, rfl⟩) <;> exact h
  · intro h
    cases e with
    | ok a => exact .inl ⟨a, h, rfl⟩
    | ub r => exact .inr ⟨r, h, rfl⟩

/-- Binds associate. -/
theorem bind_assoc (s : SetM α) (f : α → SetM β) (g : β → SetM γ) :
    (s >>= f >>= g) = s >>= fun a => f a >>= g := by
  funext e
  apply propext
  show ((∃ b, ((∃ a, s (.ok a) ∧ f a (.ok b)) ∨ ∃ r, s (.ub r) ∧ Ev.ok b = .ub r) ∧ g b e) ∨
      ∃ r, ((∃ a, s (.ok a) ∧ f a (.ub r)) ∨ ∃ r', s (.ub r') ∧ Ev.ub r = .ub r') ∧
        e = .ub r) ↔
    (∃ a, s (.ok a) ∧ ((∃ b, f a (.ok b) ∧ g b e) ∨ ∃ r, f a (.ub r) ∧ e = .ub r)) ∨
      ∃ r, s (.ub r) ∧ e = .ub r
  constructor
  · rintro (⟨b, ⟨a, ha, hb⟩ | ⟨_, _, h⟩, hg⟩ | ⟨r, ⟨a, ha, hr⟩ | ⟨r', hr', h⟩, rfl⟩)
    · exact .inl ⟨a, ha, .inl ⟨b, hb, hg⟩⟩
    · cases h
    · exact .inl ⟨a, ha, .inr ⟨r, hr, rfl⟩⟩
    · cases h
      exact .inr ⟨r, hr', rfl⟩
  · rintro (⟨a, ha, ⟨b, hb, hg⟩ | ⟨r, hr, rfl⟩⟩ | ⟨r, hr, rfl⟩)
    · exact .inl ⟨b, .inl ⟨a, ha, hb⟩, hg⟩
    · exact .inr ⟨r, .inl ⟨a, ha, hr⟩, rfl⟩
    · exact .inr ⟨r, .inr ⟨r, hr, rfl⟩, rfl⟩

/-- The set monad is a lawful monad. -/
instance : LawfulMonad SetM :=
  LawfulMonad.mk' SetM (fun s => bind_pure s) (fun a f => pure_bind a f)
    (fun s f g => bind_assoc s f g)

end SetM

/-!
Execution gives valid modules their meaning, but `fir-ref run` also runs
modules that have not been validated. So a path of a run can also end
_stuck_, defined below. A valid module never gets stuck
(ADR-2026-10-29-2009): no path of its runs is stuck, and they have an
outcome at every budget. These are the no-stuck and progress obligations of
the next section.
-/

/-- Why a path of a run is stuck: it reached a case that validation rules
out. The reason is for people. -/
structure Stuck where
  reason : String
  deriving Repr, DecidableEq

/-- A run at one fuel budget: the set of the ways it may end. Each path ends
with a result, with UB, or stuck. It is what the interpreter computes in
`ExceptT Stuck SetM`. -/
abbrev Run (O : Type) : Type := SetM (Except Stuck (Result O))

example (O : Type) : ExceptT Stuck SetM (Result O) = Run O := rfl

/-- The outcomes of a run, as a set. A stuck path is not an outcome. -/
def Run.outcomes (s : Run O) : Outcome O → Prop
  | .ret o => s (.ok (.ok (.ret o)))
  | .ub r => s (.ub r)
  | .fuelExhausted => s (.ok (.ok .fuelExhausted))

/-- A path of the run is stuck. -/
def Run.IsStuck (s : Run O) : Prop := ∃ st, s (.ok (.error st))

/-!
# Observable behaviour

A run of the interpreter takes fuel, so its set of outcomes depends on the
budget. Among the outcomes of the run at budget _n_, running out of fuel
means only that the run ran out of fuel at that budget. A function's
observable behaviour does not depend on the budget. It is what the runs show
over every budget: each return and each UB that some budget reaches, and
divergence when every budget can be exhausted. In a behaviour, the outcome
"fuel exhausted" stands for divergence.

The two meet only through the bridge lemma of the next section. The
soundness theorems of `fir-ref`'s exhaustive, scripted and sampled modes are
stated against the outcomes of the run at the budget the mode runs with, and
so is any rule that judges a run at one budget.

Reading divergence as "every budget can be exhausted" assumes that every
choice has finitely many options. Then, by König's lemma, a run that can
exhaust every budget has one infinite sequence of choices along which it
never ends. The core dialect's one choice, a choice of _w_ bits, has 2 to
the power _w_ options. An effect that a dialect adds must keep this
assumption, or come with its own definition of divergence.
-/

/-- A behaviour: a set of outcomes. -/
def Behaviour (O : Type) : Type := Outcome O → Prop

/--
The observable behaviour of a run that takes fuel. `run n` is the run with
budget `n`, in the set monad. The runs of a function of a module on its
arguments are such a run (`Func.runs`), and the function's observable
behaviour on those arguments is this set.
-/
def observable (run : Nat → Run O) : Behaviour O
  | .ret o => ∃ n, (run n).outcomes (.ret o)
  | .ub r => ∃ n, (run n).outcomes (.ub r)
  | .fuelExhausted => ∀ n, (run n).outcomes .fuelExhausted

end Fir
