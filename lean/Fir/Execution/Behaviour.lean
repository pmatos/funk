import Fir.Execution.Values
import Fir.Execution.Effects

/-!
# Outcomes

One run of a function ends in one of three ways. It returns, and an observer
sees what it returned. It hits immediate UB, for a reason. Or it runs out of
fuel, which stands for non-termination.

What an observer sees of a return is the run's _observation_. Each dialect
supplies its observations and how they refine (G0); refinement is not wired
to integer return values. In M0 the observation is the list of returned
values. A function that returns one `iN` therefore has the four outcomes of
`fir-ref`: a value, poison, UB with a reason, and fuel exhausted.
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
budget. A function's observable behaviour does not. It is what the runs show
over every budget: each return and each UB that some budget reaches, and
non-termination when every budget can be exhausted.

The interpreter (#10) must not change how a run that returns or hits UB ends
when it is given more fuel. Then the observable behaviour does not depend on
how the interpreter counts fuel, and refinement between two functions does
not depend on how many steps each takes.
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

/-!
# Refining behaviours

An outcome of the source allows an outcome of the target when:

* the source outcome is UB: UB allows anything;
* both return, and the source's observation is refined by the target's. For
  values, a poison result is refined by any value;
* both do not terminate.

A target behaviour refines a source behaviour when every target outcome is
allowed by some source outcome. So if the source can hit UB on some choice,
every target behaviour refines it (S4, ADR-2026-10-29-2008).
-/

/-- An outcome of the source allows an outcome of the target. -/
def Outcome.IsRefinedBy [HRefinement O O] : Outcome O → Outcome O → Prop
  | .ub _, _ => True
  | .ret a, .ret b => a ⊑ b
  | .fuelExhausted, .fuelExhausted => True
  | _, _ => False

instance [HRefinement O O] : HRefinement (Outcome O) (Outcome O) := ⟨Outcome.IsRefinedBy⟩

/-- Every outcome of the target behaviour is allowed by the source. -/
def Behaviour.IsRefinedBy [HRefinement O O] (src tgt : Behaviour O) : Prop :=
  ∀ t, tgt t → ∃ s, src s ∧ s ⊑ t

instance [HRefinement O O] : HRefinement (Behaviour O) (Behaviour O) :=
  ⟨Behaviour.IsRefinedBy⟩

/-- Source UB allows anything: a source that may hit UB is refined by every
target. -/
theorem Behaviour.ub_isRefinedBy [HRefinement O O] {src : Behaviour O} {r : String}
    (h : src (.ub r)) (tgt : Behaviour O) : src ⊑ tgt :=
  fun _ _ => ⟨.ub r, h, trivial⟩

/-- A returned poison is refined by any returned value. -/
theorem Outcome.poison_isRefinedBy (b : PoisonOr α) :
    (Outcome.ret (PoisonOr.poison : PoisonOr α)) ⊑ Outcome.ret b :=
  trivial

/-- Refinement of behaviours is reflexive when refinement of observations is. -/
theorem Behaviour.isRefinedBy_refl [HRefinement O O] (hO : ∀ o : O, o ⊑ o)
    (b : Behaviour O) : b ⊑ b := by
  intro t ht
  refine ⟨t, ht, ?_⟩
  cases t with
  | ret o => exact hO o
  | ub _ => trivial
  | fuelExhausted => trivial

end Fir
