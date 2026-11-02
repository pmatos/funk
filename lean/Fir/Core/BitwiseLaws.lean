import Fir.Core.WrapLaws

/-!
# The bitwise ops and shifts are lawful

`and`, `or`, `xor`, `shl`, `lshr` and `ashr` meet the obligations of the
poison classes section. They propagate poison (ADR-2026-10-30-0818), so
each meets both poison clauses, returns a result on some operands with no
poison, and is total and monotone.

None of them is ever UB, so the clause "UB only by the op's own rules"
holds at once. Each rule gives poison on a poison operand, so it is
`Strict`, as the section on the arithmetic obligations defines it, and so
it is monotone: a poison operand gives a poison result, which every result
refines, and defined operands are refined only by themselves. A shift by
`N` or more gives poison on two defined operands as well; that changes
neither argument, since a defined amount is refined only by itself. Each
returns a result on the defined operands `0` and `0`: a shift by `0` gives
its value, and at any width a poison result is a result too.
-/

namespace Fir.Core

theorem strict_andValues : Strict (w := w) andValues := fun a _ h => by
  rcases h with rfl | rfl
  · rfl
  · cases a <;> rfl

theorem strict_orValues : Strict (w := w) orValues := fun a _ h => by
  rcases h with rfl | rfl
  · rfl
  · cases a <;> rfl

theorem strict_xorValues : Strict (w := w) xorValues := fun a _ h => by
  rcases h with rfl | rfl
  · rfl
  · cases a <;> rfl

/-- A shift gives poison on a poison operand, whatever it shifts by. -/
theorem strict_shiftValues (s : BitVec w → Nat → BitVec w) : Strict (shiftValues s) :=
  fun a _ h => by
    rcases h with rfl | rfl
    · rfl
    · cases a <;> rfl

theorem strict_shlValues : Strict (w := w) shlValues := strict_shiftValues _

theorem strict_lshrValues : Strict (w := w) lshrValues := strict_shiftValues _

theorem strict_ashrValues : Strict (w := w) ashrValues := strict_shiftValues _

/-! # `and` -/

/-- `and` propagates poison: a poison operand gives only poison, and it is
never UB. -/
theorem and_propagatesPoison (w : Nat) : PropagatesPoison (d := CoreDialect) (.and w) where
  poisonOut
    | .cons _ (.cons _ .nil), h, _, hrs => by
      cases hrs
      exact ⟨strict_andValues _ _ (h.imp_right fun h => h.elim id False.elim), trivial⟩
  ubByOwnRules
    | .cons _ (.cons _ .nil), _, _, hub => nomatch hub

/-- `and` returns a result on two defined operands. -/
theorem and_returnsOnDefined (w : Nat) : ReturnsOnDefined (d := CoreDialect) (.and w) := by
  refine ⟨.cons (.value 0) (.cons (.value 0) .nil), ?_, _, rfl⟩
  rintro (h | h | h) <;> cases h

/-- `and` has an outcome on every operand vector. -/
theorem and_total (w : Nat) : OpTotal (d := CoreDialect) (.and w) := fun
  | .cons _ (.cons _ .nil) => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `and` is monotone. -/
theorem and_monotone (w : Nat) : OpMonotone (d := CoreDialect) (.and w) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
    intro e he
    cases he
    exact ⟨_, rfl, strict_andValues.isRefinedBy ha hb, trivial⟩

/-! # `or` -/

/-- `or` propagates poison. -/
theorem or_propagatesPoison (w : Nat) : PropagatesPoison (d := CoreDialect) (.or w) where
  poisonOut
    | .cons _ (.cons _ .nil), h, _, hrs => by
      cases hrs
      exact ⟨strict_orValues _ _ (h.imp_right fun h => h.elim id False.elim), trivial⟩
  ubByOwnRules
    | .cons _ (.cons _ .nil), _, _, hub => nomatch hub

/-- `or` returns a result on two defined operands. -/
theorem or_returnsOnDefined (w : Nat) : ReturnsOnDefined (d := CoreDialect) (.or w) := by
  refine ⟨.cons (.value 0) (.cons (.value 0) .nil), ?_, _, rfl⟩
  rintro (h | h | h) <;> cases h

/-- `or` has an outcome on every operand vector. -/
theorem or_total (w : Nat) : OpTotal (d := CoreDialect) (.or w) := fun
  | .cons _ (.cons _ .nil) => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `or` is monotone. -/
theorem or_monotone (w : Nat) : OpMonotone (d := CoreDialect) (.or w) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
    intro e he
    cases he
    exact ⟨_, rfl, strict_orValues.isRefinedBy ha hb, trivial⟩

/-! # `xor` -/

/-- `xor` propagates poison. -/
theorem xor_propagatesPoison (w : Nat) : PropagatesPoison (d := CoreDialect) (.xor w) where
  poisonOut
    | .cons _ (.cons _ .nil), h, _, hrs => by
      cases hrs
      exact ⟨strict_xorValues _ _ (h.imp_right fun h => h.elim id False.elim), trivial⟩
  ubByOwnRules
    | .cons _ (.cons _ .nil), _, _, hub => nomatch hub

/-- `xor` returns a result on two defined operands. -/
theorem xor_returnsOnDefined (w : Nat) : ReturnsOnDefined (d := CoreDialect) (.xor w) := by
  refine ⟨.cons (.value 0) (.cons (.value 0) .nil), ?_, _, rfl⟩
  rintro (h | h | h) <;> cases h

/-- `xor` has an outcome on every operand vector. -/
theorem xor_total (w : Nat) : OpTotal (d := CoreDialect) (.xor w) := fun
  | .cons _ (.cons _ .nil) => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `xor` is monotone. -/
theorem xor_monotone (w : Nat) : OpMonotone (d := CoreDialect) (.xor w) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
    intro e he
    cases he
    exact ⟨_, rfl, strict_xorValues.isRefinedBy ha hb, trivial⟩

/-! # `shl` -/

/-- `shl` propagates poison: a poison value or amount gives only poison,
and it is never UB. -/
theorem shl_propagatesPoison (w : Nat) : PropagatesPoison (d := CoreDialect) (.shl w) where
  poisonOut
    | .cons _ (.cons _ .nil), h, _, hrs => by
      cases hrs
      exact ⟨strict_shlValues _ _ (h.imp_right fun h => h.elim id False.elim), trivial⟩
  ubByOwnRules
    | .cons _ (.cons _ .nil), _, _, hub => nomatch hub

/-- `shl` returns a result on two defined operands. -/
theorem shl_returnsOnDefined (w : Nat) : ReturnsOnDefined (d := CoreDialect) (.shl w) := by
  refine ⟨.cons (.value 0) (.cons (.value 0) .nil), ?_, _, rfl⟩
  rintro (h | h | h) <;> cases h

/-- `shl` has an outcome on every operand vector. -/
theorem shl_total (w : Nat) : OpTotal (d := CoreDialect) (.shl w) := fun
  | .cons _ (.cons _ .nil) => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `shl` is monotone. -/
theorem shl_monotone (w : Nat) : OpMonotone (d := CoreDialect) (.shl w) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
    intro e he
    cases he
    exact ⟨_, rfl, strict_shlValues.isRefinedBy ha hb, trivial⟩

/-! # `lshr` -/

/-- `lshr` propagates poison. -/
theorem lshr_propagatesPoison (w : Nat) : PropagatesPoison (d := CoreDialect) (.lshr w) where
  poisonOut
    | .cons _ (.cons _ .nil), h, _, hrs => by
      cases hrs
      exact ⟨strict_lshrValues _ _ (h.imp_right fun h => h.elim id False.elim), trivial⟩
  ubByOwnRules
    | .cons _ (.cons _ .nil), _, _, hub => nomatch hub

/-- `lshr` returns a result on two defined operands. -/
theorem lshr_returnsOnDefined (w : Nat) : ReturnsOnDefined (d := CoreDialect) (.lshr w) := by
  refine ⟨.cons (.value 0) (.cons (.value 0) .nil), ?_, _, rfl⟩
  rintro (h | h | h) <;> cases h

/-- `lshr` has an outcome on every operand vector. -/
theorem lshr_total (w : Nat) : OpTotal (d := CoreDialect) (.lshr w) := fun
  | .cons _ (.cons _ .nil) => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `lshr` is monotone. -/
theorem lshr_monotone (w : Nat) : OpMonotone (d := CoreDialect) (.lshr w) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
    intro e he
    cases he
    exact ⟨_, rfl, strict_lshrValues.isRefinedBy ha hb, trivial⟩

/-! # `ashr` -/

/-- `ashr` propagates poison. -/
theorem ashr_propagatesPoison (w : Nat) : PropagatesPoison (d := CoreDialect) (.ashr w) where
  poisonOut
    | .cons _ (.cons _ .nil), h, _, hrs => by
      cases hrs
      exact ⟨strict_ashrValues _ _ (h.imp_right fun h => h.elim id False.elim), trivial⟩
  ubByOwnRules
    | .cons _ (.cons _ .nil), _, _, hub => nomatch hub

/-- `ashr` returns a result on two defined operands. -/
theorem ashr_returnsOnDefined (w : Nat) : ReturnsOnDefined (d := CoreDialect) (.ashr w) := by
  refine ⟨.cons (.value 0) (.cons (.value 0) .nil), ?_, _, rfl⟩
  rintro (h | h | h) <;> cases h

/-- `ashr` has an outcome on every operand vector. -/
theorem ashr_total (w : Nat) : OpTotal (d := CoreDialect) (.ashr w) := fun
  | .cons _ (.cons _ .nil) => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `ashr` is monotone. -/
theorem ashr_monotone (w : Nat) : OpMonotone (d := CoreDialect) (.ashr w) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
    intro e he
    cases he
    exact ⟨_, rfl, strict_ashrValues.isRefinedBy ha hb, trivial⟩

end Fir.Core
