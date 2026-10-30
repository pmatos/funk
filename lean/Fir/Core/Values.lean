import Fir.Core.Signature
import Fir.Execution.Refinement

/-!
The values of the core dialect. A value of `iN` is poison or an `N`-bit
vector: `⟦iN⟧ = PoisonOr (BitVec N)`. Lean's `BitVec N` exists for every `N`,
so the semantics treats every width alike (S2, ADR-2026-10-29-2007).

`ptr` has no values in M0: validation rejects every value of type `ptr`,
because their meaning waits for the memory model (S3). Its denotation is the
empty type until then.
-/

namespace Fir

/-- `⟦iN⟧` is `PoisonOr (BitVec N)`; `⟦ptr⟧` is empty in M0. -/
def Core.Ty.toType : Core.Ty → Type
  | .int w => PoisonOr (BitVec w)
  | .ptr => Empty

instance : TyDenote Core.Ty := ⟨Core.Ty.toType⟩

/-- Core values refine as `PoisonOr` values: poison is refined by any value. -/
def Core.Ty.IsRefinedBy : {t : Core.Ty} → ⟦t⟧ → ⟦t⟧ → Prop
  | .int _, a, b => PoisonOr.IsRefinedBy a b
  | .ptr, a, _ => nomatch (a : Empty)

instance : TyRefinement Core.Ty := ⟨Core.Ty.IsRefinedBy⟩

/-- The core dialect's typed values refine through the general instance,
named here because instance search does not find it for `CoreDialect`. -/
instance : HRefinement (DVal CoreDialect) (DVal CoreDialect) := instHRefinementDVal

/--
The observation of a run of a core function: the values it returns, any
number of them. A returned list is refined by a list of the same types whose
values refine it one by one.
-/
abbrev Core.Obs := List (DVal CoreDialect)

example (s t : Behaviour Core.Obs) : Prop := s ⊑ t

/-- A returned poison is refined by any returned value of its type: S4's
rule for poison, for M0's outcomes. -/
theorem Core.poison_isRefinedBy (w : Nat) (b : PoisonOr (BitVec w)) :
    (Outcome.ret [⟨.int w, .poison⟩] : Outcome Core.Obs) ⊑
      (Outcome.ret [⟨.int w, b⟩] : Outcome Core.Obs) :=
  ⟨⟨rfl, trivial⟩, trivial⟩

/-- Refinement of core values is reflexive. -/
theorem Core.Ty.isRefinedBy_refl : ∀ {t : Core.Ty} (a : ⟦t⟧), Core.Ty.IsRefinedBy a a
  | .int _, a => PoisonOr.isRefinedBy_refl a
  | .ptr, a => nomatch (a : Empty)

/-- Refinement of core values is transitive. -/
theorem Core.Ty.isRefinedBy_trans : ∀ {t : Core.Ty} {a b c : ⟦t⟧},
    Core.Ty.IsRefinedBy a b → Core.Ty.IsRefinedBy b c → Core.Ty.IsRefinedBy a c
  | .int _, _, _, _, hab, hbc => PoisonOr.isRefinedBy_trans hab hbc
  | .ptr, a, _, _, _, _ => nomatch (a : Empty)

/-- Refinement of M0's observations is reflexive. -/
theorem Core.Obs.isRefinedBy_refl : ∀ o : Core.Obs, o ⊑ o
  | [] => trivial
  | ⟨_, v⟩ :: os => ⟨⟨rfl, Core.Ty.isRefinedBy_refl v⟩, Core.Obs.isRefinedBy_refl os⟩

/-- Refinement of M0's observations is transitive. -/
theorem Core.Obs.isRefinedBy_trans {a b c : Core.Obs} : a ⊑ b → b ⊑ c → a ⊑ c :=
  List.isRefinedBy_trans (DVal.isRefinedBy_trans (d := CoreDialect) Core.Ty.isRefinedBy_trans)

/-- Refinement of M0 behaviours is transitive. -/
theorem Core.behaviour_isRefinedBy_trans {a b c : Behaviour Core.Obs} :
    a ⊑ b → b ⊑ c → a ⊑ c :=
  Behaviour.isRefinedBy_trans Core.Obs.isRefinedBy_trans

/--
The runs of a core function with parameter types `ts`: its run on each
argument vector of those types. A value of `iN` may be poison, so poison
arguments are part of the type, and function refinement covers them
(choice 23).
-/
abbrev Core.FuncRuns (ts : List Core.Ty) : Type := Fir.FuncRuns (HVector toType ts) Core.Obs

/-- Refinement of M0 functions is transitive. -/
theorem Core.funcRuns_isRefinedBy_trans {f g h : Core.FuncRuns ts} :
    f ⊑ g → g ⊑ h → f ⊑ h :=
  FuncRuns.isRefinedBy_trans Core.Obs.isRefinedBy_trans

/-- Refinement of M0 functions is reflexive. -/
theorem Core.funcRuns_isRefinedBy_refl (f : Core.FuncRuns ts) : f ⊑ f :=
  FuncRuns.isRefinedBy_refl Core.Obs.isRefinedBy_refl f

end Fir
