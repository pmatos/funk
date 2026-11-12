import Fir.Core.Semantics
import Fir.Core.Poison

/-!
# Return and unreachable are lawful

`ret` and `unreachable` are exceptions to poison propagation
(ADR-2026-10-29-2006), so of the obligations of the poison classes section
they meet two: they are total and monotone. Both look at the op's exit.

`ret` sends control back to the caller on every operand vector, poison or
not. So its exit is the same on operands that refine others, which is all
that monotonicity asks of a terminator: the values it returns are its
operands, and the interpreter passes them on as they are.

`unreachable` is UB on every run, which is an exit too, so it is total.
It has no operands, so it is monotone: its exit on any operands is its
exit on the same, empty, vector, and UB is refined by anything.
-/

namespace Fir.Core

/-- `ret` has an exit on every operand vector. -/
theorem ret_total (ts : List Ty) : OpTotal (d := CoreDialect) (.ret ts) :=
  fun _ => ⟨(fun h => nomatch h), fun _ => ⟨_, rfl⟩⟩

/-- `ret` is monotone: on any operands, it returns. -/
theorem ret_monotone (ts : List Ty) : OpMonotone (d := CoreDialect) (.ret ts) :=
  fun _ _ _ => ⟨(fun h => nomatch h), fun _ e he => by cases he; exact ⟨_, rfl, rfl⟩⟩

/-- In the set monad, `unreachable` ends in UB, and in nothing else. -/
theorem unreachable_exit (args : HVector toType (Fir.sig (d := CoreDialect) .unreachable))
    (e : Ev Exit) :
    DialectDenote.exit (m := SetM) (d := CoreDialect) .unreachable args e ↔
      e = unreachableExit :=
  Iff.rfl

/-- `unreachable` has an exit on every operand vector: UB. -/
theorem unreachable_total : OpTotal (d := CoreDialect) .unreachable :=
  fun args => ⟨(fun h => nomatch h), fun _ => ⟨_, (unreachable_exit args _).2 rfl⟩⟩

/-- `unreachable` is monotone: on any operands, it is UB, which allows
anything. -/
theorem unreachable_monotone : OpMonotone (d := CoreDialect) .unreachable :=
  fun args _ _ => ⟨(fun h => nomatch h), fun _ _ _ => ⟨_, (unreachable_exit args _).2 rfl, trivial⟩⟩

end Fir.Core
