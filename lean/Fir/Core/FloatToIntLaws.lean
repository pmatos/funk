import Fir.Core.Semantics
import Fir.Core.WidthLaws

/-!
# Conversions from floats to integers are lawful

`fptosi` and `fptoui`, from every format to every width, meet the
obligations of the poison classes section. Each propagates poison
(ADR-2026-10-29-2006), so it meets both poison clauses, returns a result
on an operand that is not poison, and is total and monotone.

Neither is ever UB, so the clause "UB only by the op's own rules" holds at
once. Each is monotone because its rule gives poison on poison, a strict
rule as the width changes and the bit casts have. Unlike them, each may
give poison on a defined operand, an integer out of range, an infinity or
a NaN, so neither meets the obligation of no poison: each declares
`mayPoison`, and the section on the effect obligations needs nothing of it.
-/

namespace Fir.Core

section
variable (e m n : Nat)

/-- The op instance of `fptosi`, with `signed`, or of `fptoui`, from
`float<e,m>` to `iN`. -/
def floatToIntOp : Bool → Op
  | true => .fptosi e m n
  | false => .fptoui e m n

theorem unaryStrict_floatToInt (signed : Bool) :
    UnaryStrict (floatToInt (n := n) e m signed) := rfl

/-- `fptosi` and `fptoui` propagate poison: a poison operand gives only a
poison result, and they are never UB. -/
theorem floatToInt_propagatesPoison (signed : Bool) :
    PropagatesPoison (d := CoreDialect) (floatToIntOp e m n signed) := by
  cases signed <;> exact {
    poisonOut := fun
      | .cons a .nil, h, _, hrs => by
        cases hrs
        obtain rfl : a = .poison := h.elim id False.elim
        exact ⟨rfl, trivial⟩
    ubByOwnRules := fun
      | .cons _ .nil, _, _, hub => nomatch hub }

/-- `fptosi` and `fptoui` return a result on a defined operand. -/
theorem floatToInt_returnsOnDefined (signed : Bool) :
    ReturnsOnDefined (d := CoreDialect) (floatToIntOp e m n signed) := by
  cases signed <;>
  · refine ⟨.cons (.value 0) .nil, ?_, _, rfl⟩
    rintro (h | h) <;> cases h

/-- `fptosi` and `fptoui` have an outcome on every operand. -/
theorem floatToInt_total (signed : Bool) :
    OpTotal (d := CoreDialect) (floatToIntOp e m n signed) := by
  cases signed <;> exact fun
    | .cons _ .nil => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `fptosi` and `fptoui` are monotone. -/
theorem floatToInt_monotone (signed : Bool) :
    OpMonotone (d := CoreDialect) (floatToIntOp e m n signed) := by
  cases signed <;>
  · intro args args' h
    refine ⟨fun _ => ?_, fun h => nomatch h⟩
    match args, args', h with
    | .cons a .nil, .cons a' .nil, ⟨ha, _⟩ =>
      intro r hr
      cases hr
      exact ⟨_, rfl, (unaryStrict_floatToInt e m n _).isRefinedBy ha, trivial⟩

end

end Fir.Core
