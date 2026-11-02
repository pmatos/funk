import Fir.Core.ArithLaws

/-!
# Addition, subtraction and multiplication are lawful

`add`, `sub` and `mul`, with each of the four combinations of their flags,
meet the obligations of the poison classes section. They propagate poison
(ADR-2026-10-30-0818), so each meets both poison clauses, returns a result
on some operands with no poison, and is total and monotone.

None of them is ever UB, so the clause "UB only by the op's own rules"
holds at once. A poison operand gives poison whatever the flags, since a
flag is checked only on two values. Each is monotone because a poison
operand gives a poison result, which every result refines, and defined
operands are refined only by themselves. The proofs rest on two facts of
any binary rule that gives poison on a poison operand, as these three do:
it gives poison there, and so it is monotone.
-/

namespace Fir.Core

/-- A binary rule on values of `iN` gives poison on a poison operand. -/
def Strict (g : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w)) : Prop :=
  ∀ a b, (a = .poison ∨ b = .poison) → g a b = .poison

/-- A rule that gives poison on a poison operand gives, on operands that
refine others, a result that refines theirs. -/
theorem Strict.isRefinedBy {g : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w)}
    (hg : Strict g) {a b a' b' : PoisonOr (BitVec w)} (ha : a ⊑ a') (hb : b ⊑ b') :
    g a b ⊑ g a' b' := by
  cases a with
  | poison => rw [hg _ _ (.inl rfl)]; trivial
  | value x =>
    cases b with
    | poison => rw [hg _ _ (.inr rfl)]; trivial
    | value y =>
      cases a' with
      | poison => exact ha.elim
      | value x' =>
        cases b' with
        | poison => exact hb.elim
        | value y' =>
          have hx : x = x' := ha
          have hy : y = y' := hb
          subst hx hy
          exact PoisonOr.isRefinedBy_refl _

theorem strict_addValues : Strict (w := w) addValues := fun _ _ h => addValues_poison h

theorem strict_subValues : Strict (w := w) subValues := fun a _ h => by
  rcases h with rfl | rfl
  · rfl
  · cases a <;> rfl

theorem strict_mulValues : Strict (w := w) mulValues := fun a _ h => by
  rcases h with rfl | rfl
  · rfl
  · cases a <;> rfl

/-- The flags keep a rule strict: they are checked only on two values. -/
theorem Strict.wrapValues {v : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w)}
    (hv : Strict v) (f : WrapFlags) (u s : BitVec w → BitVec w → Bool) :
    Strict (wrapValues f u s v) := fun a _ h => by
  rcases h with rfl | rfl
  · exact hv _ _ (.inl rfl)
  · cases a <;> exact hv _ _ (.inr rfl)

theorem strict_addWith (f : WrapFlags) : Strict (w := w) (addWith f) :=
  strict_addValues.wrapValues f _ _

theorem strict_subWith (f : WrapFlags) : Strict (w := w) (subWith f) :=
  strict_subValues.wrapValues f _ _

theorem strict_mulWith (f : WrapFlags) : Strict (w := w) (mulWith f) :=
  strict_mulValues.wrapValues f _ _

/-! # `add` -/

/-- `add` propagates poison, with any flags: a poison operand gives only
poison, and it is never UB. -/
theorem add_propagatesPoison (w : Nat) (f : WrapFlags) :
    PropagatesPoison (d := CoreDialect) (.add w f) where
  poisonOut
    | .cons _ (.cons _ .nil), h, _, hrs => by
      cases hrs
      exact ⟨strict_addWith f _ _ (h.imp_right fun h => h.elim id False.elim), trivial⟩
  ubByOwnRules
    | .cons _ (.cons _ .nil), _, _, hub => nomatch hub

/-- `add` returns a result on two defined operands, with any flags. -/
theorem add_returnsOnDefined (w : Nat) (f : WrapFlags) :
    ReturnsOnDefined (d := CoreDialect) (.add w f) := by
  refine ⟨.cons (.value 0) (.cons (.value 0) .nil), ?_, _, rfl⟩
  rintro (h | h | h) <;> cases h

/-- `add` has an outcome on every operand vector, with any flags. -/
theorem add_total (w : Nat) (f : WrapFlags) : OpTotal (d := CoreDialect) (.add w f) := fun
  | .cons _ (.cons _ .nil) => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `add` is monotone, with any flags. -/
theorem add_monotone (w : Nat) (f : WrapFlags) : OpMonotone (d := CoreDialect) (.add w f) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
    intro e he
    cases he
    exact ⟨_, rfl, (strict_addWith f).isRefinedBy ha hb, trivial⟩

/-! # `sub` -/

/-- `sub` propagates poison, with any flags. -/
theorem sub_propagatesPoison (w : Nat) (f : WrapFlags) :
    PropagatesPoison (d := CoreDialect) (.sub w f) where
  poisonOut
    | .cons _ (.cons _ .nil), h, _, hrs => by
      cases hrs
      exact ⟨strict_subWith f _ _ (h.imp_right fun h => h.elim id False.elim), trivial⟩
  ubByOwnRules
    | .cons _ (.cons _ .nil), _, _, hub => nomatch hub

/-- `sub` returns a result on two defined operands, with any flags. -/
theorem sub_returnsOnDefined (w : Nat) (f : WrapFlags) :
    ReturnsOnDefined (d := CoreDialect) (.sub w f) := by
  refine ⟨.cons (.value 0) (.cons (.value 0) .nil), ?_, _, rfl⟩
  rintro (h | h | h) <;> cases h

/-- `sub` has an outcome on every operand vector, with any flags. -/
theorem sub_total (w : Nat) (f : WrapFlags) : OpTotal (d := CoreDialect) (.sub w f) := fun
  | .cons _ (.cons _ .nil) => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `sub` is monotone, with any flags. -/
theorem sub_monotone (w : Nat) (f : WrapFlags) : OpMonotone (d := CoreDialect) (.sub w f) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
    intro e he
    cases he
    exact ⟨_, rfl, (strict_subWith f).isRefinedBy ha hb, trivial⟩

/-! # `mul` -/

/-- `mul` propagates poison, with any flags. -/
theorem mul_propagatesPoison (w : Nat) (f : WrapFlags) :
    PropagatesPoison (d := CoreDialect) (.mul w f) where
  poisonOut
    | .cons _ (.cons _ .nil), h, _, hrs => by
      cases hrs
      exact ⟨strict_mulWith f _ _ (h.imp_right fun h => h.elim id False.elim), trivial⟩
  ubByOwnRules
    | .cons _ (.cons _ .nil), _, _, hub => nomatch hub

/-- `mul` returns a result on two defined operands, with any flags. -/
theorem mul_returnsOnDefined (w : Nat) (f : WrapFlags) :
    ReturnsOnDefined (d := CoreDialect) (.mul w f) := by
  refine ⟨.cons (.value 0) (.cons (.value 0) .nil), ?_, _, rfl⟩
  rintro (h | h | h) <;> cases h

/-- `mul` has an outcome on every operand vector, with any flags. -/
theorem mul_total (w : Nat) (f : WrapFlags) : OpTotal (d := CoreDialect) (.mul w f) := fun
  | .cons _ (.cons _ .nil) => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `mul` is monotone, with any flags. -/
theorem mul_monotone (w : Nat) (f : WrapFlags) : OpMonotone (d := CoreDialect) (.mul w f) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
    intro e he
    cases he
    exact ⟨_, rfl, (strict_mulWith f).isRefinedBy ha hb, trivial⟩

end Fir.Core
