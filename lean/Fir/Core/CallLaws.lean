import Fir.Core.Semantics
import Fir.Core.Poison

/-!
# Call's stand-in is lawful

`call` is an exception to poison propagation (ADR-2026-10-30-0818), so of
the obligations of the poison classes section it meets two: it is total
and monotone. Both look at its `denote` in the set monad, which for
`call` is only its stand-in, `callStandIn`: immediate UB on every operand
vector. The interpreter never runs it (the section on calls).

* _Totality._ The stand-in has an outcome on every operand vector, UB, at
  every type, even at a result type with no values.
* _Monotonicity._ UB on the original operands allows anything, so it
  allows whatever happens on operands that refine them.

So these two hold of `call`, trivially, and carry no information about
calls. The stand-in is the top of the refinement order: every
computation refines it (`call_isRefinedBy`), so a statement that reads it
as a source, such as a rewrite rule from `call` to `const 0`, would hold
and say nothing about a real call (ADR-2026-11-02-1156). What a call does
is its callee's run, and the facts about it are stated about the runs of
functions: no path of a valid core function's run is stuck, and it has
an outcome at every budget, calls and recursion included (the section on
every valid core function); and refining a call's arguments, or its
callee, refines its caller (the section on refinement through core
calls).
-/

namespace Fir.Core

/-- In the set monad, `call`'s stand-in ends only in UB. -/
theorem call_denote (g : Name) (ts rs : List Ty) (args : HVector toType ts)
    (e : Ev (HVector toType rs)) :
    DialectDenote.denote (m := SetM) (d := CoreDialect) (.call g ts rs) args e ↔
      e = .ub callStandInReason :=
  Iff.rfl

/-- `call`'s stand-in has an outcome on every operand vector: UB. -/
theorem call_total (g : Name) (ts rs : List Ty) : OpTotal (d := CoreDialect) (.call g ts rs) :=
  fun args => ⟨fun _ => ⟨_, (call_denote g ts rs args _).2 rfl⟩, fun h => nomatch h⟩

/-- `call`'s stand-in is monotone: UB on the original operands allows
whatever happens on refined ones. -/
theorem call_monotone (g : Name) (ts rs : List Ty) :
    OpMonotone (d := CoreDialect) (.call g ts rs) :=
  fun args _ _ => ⟨fun _ _ _ => ⟨_, (call_denote g ts rs args _).2 rfl, trivial⟩,
    fun h => nomatch h⟩

/-- `call`'s stand-in is the top of the refinement order: every
computation of its result types refines it. So a statement that reads it
as a source holds for every target and says nothing about a real call. -/
theorem call_isRefinedBy (g : Name) (ts rs : List Ty) (args : HVector toType ts)
    (t : SetM (HVector toType rs)) :
    SetM.IsRefinedBy (HVector.Forall₂ TyRefinement.IsRefinedBy)
      (DialectDenote.denote (m := SetM) (d := CoreDialect) (.call g ts rs) args) t :=
  fun _ _ => ⟨_, (call_denote g ts rs args _).2 rfl, trivial⟩

end Fir.Core
