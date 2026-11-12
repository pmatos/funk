import Fir.Core.Semantics
import Fir.Core.WidthLaws

/-!
# Bit casts are lawful

The two bit casts, from a float to its bits and from bits to a float,
meet the obligations of the poison classes section, at every float
format, valid or not. They propagate poison (ADR-2026-10-29-2006), so
each meets both poison clauses, returns a result on an operand that is
not poison, and is total and monotone.

Neither is ever UB, so the clause "UB only by the op's own rules" holds at
once. Each is monotone because its rule gives poison on poison, a strict
rule as the width changes have, which the section on width change
obligations proves monotone.
-/

namespace Fir.Core

theorem unaryStrict_bitcastValue : UnaryStrict (m := w) (n := w) bitcastValue := rfl

/-! # From a float to its bits -/

/-- `bitcast` from a float to its bits propagates poison, at every
format: a poison operand gives only poison, and it is never UB. -/
theorem toBits_propagatesPoison (e m : Nat) : PropagatesPoison (d := CoreDialect) (.toBits e m) where
  poisonOut
    | .cons a .nil, h, _, hrs => by
      cases hrs
      obtain rfl : a = .poison := h.elim id False.elim
      exact ⟨rfl, trivial⟩
  ubByOwnRules
    | .cons _ .nil, _, _, hub => nomatch hub

/-- `bitcast` from a float to its bits returns a result on a defined
operand, at every format. -/
theorem toBits_returnsOnDefined (e m : Nat) : ReturnsOnDefined (d := CoreDialect) (.toBits e m) := by
  refine ⟨.cons (.value 0) .nil, ?_, _, rfl⟩
  rintro (h | h) <;> cases h

/-- `bitcast` from a float to its bits has an outcome on every operand. -/
theorem toBits_total (e m : Nat) : OpTotal (d := CoreDialect) (.toBits e m) := fun
  | .cons _ .nil => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `bitcast` from a float to its bits is monotone, at every format. -/
theorem toBits_monotone (e m : Nat) : OpMonotone (d := CoreDialect) (.toBits e m) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a .nil, .cons a' .nil, ⟨ha, _⟩ =>
    intro r hr
    cases hr
    exact ⟨_, rfl, unaryStrict_bitcastValue.isRefinedBy ha, trivial⟩

/-! # From bits to a float -/

/-- `bitcast` from bits to a float propagates poison, at every format. -/
theorem ofBits_propagatesPoison (e m : Nat) : PropagatesPoison (d := CoreDialect) (.ofBits e m) where
  poisonOut
    | .cons a .nil, h, _, hrs => by
      cases hrs
      obtain rfl : a = .poison := h.elim id False.elim
      exact ⟨rfl, trivial⟩
  ubByOwnRules
    | .cons _ .nil, _, _, hub => nomatch hub

/-- `bitcast` from bits to a float returns a result on a defined operand,
at every format. -/
theorem ofBits_returnsOnDefined (e m : Nat) : ReturnsOnDefined (d := CoreDialect) (.ofBits e m) := by
  refine ⟨.cons (.value 0) .nil, ?_, _, rfl⟩
  rintro (h | h) <;> cases h

/-- `bitcast` from bits to a float has an outcome on every operand. -/
theorem ofBits_total (e m : Nat) : OpTotal (d := CoreDialect) (.ofBits e m) := fun
  | .cons _ .nil => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `bitcast` from bits to a float is monotone, at every format. -/
theorem ofBits_monotone (e m : Nat) : OpMonotone (d := CoreDialect) (.ofBits e m) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a .nil, .cons a' .nil, ⟨ha, _⟩ =>
    intro r hr
    cases hr
    exact ⟨_, rfl, unaryStrict_bitcastValue.isRefinedBy ha, trivial⟩

end Fir.Core
