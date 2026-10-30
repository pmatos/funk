import Fir.Execution.Fuel

/-!
# Refining behaviours

An outcome of the source allows an outcome of the target when:

* the source outcome is UB: UB allows anything;
* both return, and the source's observation is refined by the target's. For
  values, a poison result is refined by any value;
* both diverge.

A target behaviour refines a source behaviour when every target outcome is
allowed by some source outcome. So if the source can hit UB on some choice,
every target behaviour refines it (S4, ADR-2026-10-29-2008).

An empty target behaviour, with no outcome at all, refines every source,
and a target that loses some of its paths refines more sources than it
should. The obligations of the previous section rule both out for a valid
function: progress, so its behaviour is never empty, and no stuck path,
which with every op total means that no path is lost.
-/

namespace Fir

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

variable [HRefinement O O]

/-- Refinement of outcomes is reflexive when refinement of observations is. -/
theorem Outcome.isRefinedBy_refl (hO : ∀ o : O, o ⊑ o) : ∀ t : Outcome O, t ⊑ t
  | .ret o => hO o
  | .ub _ | .fuelExhausted => trivial

/-- Refinement of outcomes is transitive when refinement of observations is. -/
theorem Outcome.isRefinedBy_trans (hO : ∀ {a b c : O}, a ⊑ b → b ⊑ c → a ⊑ c) :
    ∀ {s m t : Outcome O}, s ⊑ m → m ⊑ t → s ⊑ t
  | .ub _, _, _, _, _ => trivial
  | .ret _, .ret _, .ret _, h₁, h₂ => hO h₁ h₂
  | .fuelExhausted, .fuelExhausted, .fuelExhausted, _, _ => trivial
  | .ret _, .ub _, _, h, _ | .ret _, .fuelExhausted, _, h, _
  | .fuelExhausted, .ret _, _, h, _ | .fuelExhausted, .ub _, _, h, _ => h.elim
  | .ret _, .ret _, .ub _, _, h | .ret _, .ret _, .fuelExhausted, _, h
  | .fuelExhausted, .fuelExhausted, .ret _, _, h
  | .fuelExhausted, .fuelExhausted, .ub _, _, h => h.elim

/-- Refinement of behaviours is reflexive when refinement of observations is. -/
theorem Behaviour.isRefinedBy_refl (hO : ∀ o : O, o ⊑ o) (b : Behaviour O) : b ⊑ b :=
  fun t ht => ⟨t, ht, Outcome.isRefinedBy_refl hO t⟩

/-- Refinement of behaviours is transitive when refinement of observations is,
so a pipeline of correct passes is correct. -/
theorem Behaviour.isRefinedBy_trans (hO : ∀ {a b c : O}, a ⊑ b → b ⊑ c → a ⊑ c)
    {a b c : Behaviour O} (hab : a ⊑ b) (hbc : b ⊑ c) : a ⊑ c := fun t ht =>
  let ⟨m, hm, hmt⟩ := hbc t ht
  let ⟨s, hs, hsm⟩ := hab m hm
  ⟨s, hs, Outcome.isRefinedBy_trans hO hsm hmt⟩

/-!
# Refining functions

A function's runs are its runs on each argument vector. A target function
refines a source function of the same type when, for each argument vector,
the target's observable behaviour refines the source's. Both run on the
same arguments, and every argument vector of the parameter types counts:
since a value of `iN` may be poison, so may any argument.
-/

/-- The runs of a function: for each argument vector, its run at each fuel
budget. #10 defines them for each function of a valid module, with `A` the
argument vectors of its parameter types, `HVector toType ts`. For the core
dialect, `Core.FuncRuns ts` fixes `A` so. -/
def FuncRuns (A O : Type) : Type := A → Nat → Run O

/-- The target function refines the source function: on every argument
vector, poison included, its observable behaviour refines the source's. -/
def FuncRuns.IsRefinedBy (src tgt : FuncRuns A O) : Prop :=
  ∀ a, observable (src a) ⊑ observable (tgt a)

instance : HRefinement (FuncRuns A O) (FuncRuns A O) := ⟨FuncRuns.IsRefinedBy⟩

/-- Refinement of functions is reflexive when refinement of observations is. -/
theorem FuncRuns.isRefinedBy_refl (hO : ∀ o : O, o ⊑ o) (f : FuncRuns A O) : f ⊑ f :=
  fun a => Behaviour.isRefinedBy_refl hO (observable (f a))

/-- Refinement of functions is transitive when refinement of observations is. -/
theorem FuncRuns.isRefinedBy_trans (hO : ∀ {a b c : O}, a ⊑ b → b ⊑ c → a ⊑ c)
    {f g h : FuncRuns A O} (hfg : f ⊑ g) (hgh : g ⊑ h) : f ⊑ h :=
  fun a => Behaviour.isRefinedBy_trans hO (hfg a) (hgh a)

end Fir
