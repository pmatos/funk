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

So these two hold of `call`, and say nothing about calls. What a call
does is its callee's run, and the facts about it are stated about the
runs of functions: no path of a valid core function's run is stuck, and
it has an outcome at every budget, calls and recursion included (the
section on every valid core function).
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

end Fir.Core
