import Fir.Core.Signature
import Fir.Execution.Refinement
import Fir.Memory.Model

/-!
The values of the core dialect, defined below, how they refine, and what
an observer sees of a core function's return. A value of a float type is
its raw bit pattern, as a value of an integer type is: which bits an op
gives, a NaN's among them, is the op's rule (ADR-2026-11-09-1549). A value
of a pointer type `ptr<N>` is poison or a pointer of the memory model: the
allocation it has provenance for, if any, and an offset into it, in the
units of the memory `N` (ADR-2026-11-09-1542). Which memory a pointer
belongs to is its type's business, so the value itself does not name it.
-/

namespace Fir

/-- `⟦iN⟧` is `PoisonOr (BitVec N)`, `⟦float<e,m>⟧` is
`PoisonOr (BitVec (1 + e + m))`, and `⟦ptr<N>⟧` is `PoisonOr Pointer`. -/
def Core.Ty.toType : Core.Ty → Type
  | .int w => PoisonOr (BitVec w)
  | .float e m => PoisonOr (BitVec (Core.floatWidth e m))
  | .ptr _ => PoisonOr Memory.Pointer

instance : TyDenote Core.Ty := ⟨Core.Ty.toType⟩

/-- Core values refine as `PoisonOr` values: poison is refined by any value,
a bit pattern only by itself, and a pointer only by itself, its provenance
and its offset alike. -/
def Core.Ty.IsRefinedBy : {t : Core.Ty} → ⟦t⟧ → ⟦t⟧ → Prop
  | .int _, a, b => PoisonOr.IsRefinedBy a b
  | .float _ _, a, b => PoisonOr.IsRefinedBy a b
  | .ptr _, a, b => PoisonOr.IsRefinedBy a b

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
  | .float _ _, a => PoisonOr.isRefinedBy_refl a
  | .ptr _, a => PoisonOr.isRefinedBy_refl a

/-- Refinement of core values is transitive. -/
theorem Core.Ty.isRefinedBy_trans : ∀ {t : Core.Ty} {a b c : ⟦t⟧},
    Core.Ty.IsRefinedBy a b → Core.Ty.IsRefinedBy b c → Core.Ty.IsRefinedBy a c
  | .int _, _, _, _, hab, hbc => PoisonOr.isRefinedBy_trans hab hbc
  | .float _ _, _, _, _, hab, hbc => PoisonOr.isRefinedBy_trans hab hbc
  | .ptr _, _, _, _, hab, hbc => PoisonOr.isRefinedBy_trans hab hbc

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
argument vector of those types. A value of every core type may be poison,
so poison arguments are part of the type, and function refinement covers
them
(the section on refining functions).
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
