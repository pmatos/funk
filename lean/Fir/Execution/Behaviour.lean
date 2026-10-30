import Fir.Execution.Values
import Fir.Execution.Effects

/-!
# Outcomes

One run of a function ends in one of three ways. It returns, and an observer
sees what it returned. It hits immediate UB, for a reason. Or it runs out of
fuel.

What an observer sees of a return is the run's _observation_. Each dialect
supplies its observations and how they refine (G0); refinement is not wired
to integer return values. In M0 the observation is the list of returned
values, each a value or poison, since a function may return any number of
values (ADR-2026-10-30-0816). A function that returns one `iN` therefore has
the four outcomes of `fir-ref`: a value, poison, UB with a reason, and fuel
exhausted. The reason that UB carries is for people: refinement ignores it.

This outcome type is M0's. M0 has no I/O, so a run shows nothing to an
observer until it ends. When the external calls of S4 (ADR-2026-10-29-2008)
arrive, an observer also sees the calls a run makes, and an outcome becomes
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

/-- How a run ends when it does not hit UB: it returns, or runs out of fuel. -/
inductive Result (O : Type) where
  | ret (o : O)
  | fuelExhausted
  deriving Repr, DecidableEq

/-!
# Behaviour as a set of outcomes

`freeze` of poison may choose any value, so one function on one input can
run in many ways. Its behaviour is the set of outcomes over all choices
(ADR-2026-10-29-2017). That set is what the interpreter computes when it runs
in the set monad below. A computation in it is the set of the ways it may
end: with a result, or with UB. `choose` may give any bits, and `ub` ends the
computation. `fir-ref`'s exhaustive and scripted modes compute this set, or
one member of it, and #14 proves that they do.
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

/-- The outcomes of a run, as a set. -/
def outcomes (s : SetM (Result O)) : Outcome O → Prop
  | .ret o => s (.ok (.ret o))
  | .ub r => s (.ub r)
  | .fuelExhausted => s (.ok .fuelExhausted)

end SetM

/-!
# Observable behaviour

A run of the interpreter takes fuel, so its set of outcomes depends on the
budget. In `(run n).outcomes`, `fuelExhausted` means only that the run ran out
of fuel at budget `n`. A function's observable behaviour does not depend on
the budget. It is what the runs show over every budget: each return and each
UB that some budget reaches, and divergence when every budget can be
exhausted. In a behaviour, `fuelExhausted` stands for divergence.

The two meet only through the bridge lemma `observable_eq_at` of the next
section. #14's soundness theorems for `fir-ref`'s exhaustive and scripted
modes are stated against `(run n).outcomes`, for the budget the mode runs
with, and so is any rule that judges a run at one budget.

Reading divergence as "every budget can be exhausted" assumes that every
choice has finitely many options. Then, by König's lemma, a run that can
exhaust every budget has one infinite sequence of choices along which it
never ends. The core dialect's one choice, `choose w`, has `2^w` options. An
effect that a dialect adds must keep this assumption, or come with its own
definition of divergence.

Execution is defined for valid modules only: a run in `SetM` has no way to
end other than a return, UB or fuel exhaustion. The executable interpreter
of #10 also runs on modules that have not been validated. It wraps each run
in an error layer outside `SetM`, such as `Except` with a reason. A run that
reaches a case that validation rules out, such as an undefined value or an
operand of the wrong type, ends in that layer: it is _stuck_, and `fir-ref`
reports it as such. A stuck run is never an empty set of outcomes, and never
UB. A valid module never gets stuck (ADR-2026-10-29-2030): its runs have an
outcome at every budget, the progress obligation of the next section.
-/

/-- A behaviour: a set of outcomes. -/
def Behaviour (O : Type) : Type := Outcome O → Prop

/--
The observable behaviour of a run that takes fuel. `run n` is the run with
budget `n`, in the set monad. #10 defines the run of a function on its
arguments, and its observable behaviour is this set.
-/
def observable (run : Nat → SetM (Result O)) : Behaviour O
  | .ret o => ∃ n, (run n).outcomes (.ret o)
  | .ub r => ∃ n, (run n).outcomes (.ub r)
  | .fuelExhausted => ∀ n, (run n).outcomes .fuelExhausted

end Fir
