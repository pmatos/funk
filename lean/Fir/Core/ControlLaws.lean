import Fir.Core.Semantics
import Fir.Core.Poison

/-!
# Return is lawful

`ret` is an exception to poison propagation (ADR-2026-10-30-0818), so of
the obligations of the poison classes section it meets two: it is total
and monotone. Both look at its exit, which sends control back to the caller
on every operand vector, poison or not. So its exit is the same on operands
that refine others, which is all that monotonicity asks of a terminator:
the values it returns are its operands, and the interpreter passes them on
as they are.
-/

namespace Fir.Core

/-- `ret` has an exit on every operand vector. -/
theorem ret_total (ts : List Ty) : OpTotal (d := CoreDialect) (.ret ts) :=
  fun _ => ⟨(fun h => nomatch h), fun _ => ⟨_, rfl⟩⟩

/-- `ret` is monotone: on any operands, it returns. -/
theorem ret_monotone (ts : List Ty) : OpMonotone (d := CoreDialect) (.ret ts) :=
  fun _ _ _ => ⟨(fun h => nomatch h), fun _ e he => by cases he; exact ⟨_, rfl, rfl⟩⟩

end Fir.Core
