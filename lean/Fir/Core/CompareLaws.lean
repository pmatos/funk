import Fir.Core.Semantics
import Fir.Core.Poison

/-!
# Comparison and selection are lawful

`icmp`, with each of its ten predicates, and `select` meet the obligations
of the poison classes section. `icmp` propagates poison
(ADR-2026-10-30-0818), so it meets both poison clauses, returns a result on
some operands with no poison, and is total and monotone. `select` is an
exception, with a rule of its own for poison, so of those obligations it
meets two: it is total and monotone.

Neither op is ever UB: each has one outcome, a result, on every operand
vector, so each is total, and the clause "UB only by the op's own rules"
holds of `icmp` at once. `icmp` returns a result on the defined operands
`0` and `0`. It is
monotone because a poison operand gives a poison result, which every
result refines, and defined operands are refined only by themselves.

`select` is monotone for a reason of its own. A poison condition gives
poison, which every result refines. A defined condition is refined only by
itself, so on operands that refine others, `select` chooses the same
operand, and that operand refines the one it chose before. This holds
whatever the operand not chosen is, poison included.
-/

namespace Fir.Core

/-! # `icmp` -/

/-- A poison operand of `icmp` gives a poison `i1`. -/
theorem icmpValues_poison (p : Pred) {a b : PoisonOr (BitVec w)} (h : a = .poison ∨ b = .poison) :
    icmpValues p a b = .poison := by
  rcases h with rfl | rfl
  · rfl
  · cases a <;> rfl

/-- `icmp` on operands that refine others gives an `i1` that refines
theirs. -/
theorem icmpValues_isRefinedBy (p : Pred) {a b a' b' : PoisonOr (BitVec w)} (ha : a ⊑ a')
    (hb : b ⊑ b') : icmpValues p a b ⊑ icmpValues p a' b' := by
  cases a with
  | poison => trivial
  | value x =>
    cases b with
    | poison => trivial
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

/-- `icmp` propagates poison, with every predicate: a poison operand gives
only a poison `i1`, and it is never UB. -/
theorem icmp_propagatesPoison (p : Pred) (w : Nat) :
    PropagatesPoison (d := CoreDialect) (.icmp p w) where
  poisonOut
    | .cons _ (.cons _ .nil), h, _, hrs => by
      cases hrs
      exact ⟨icmpValues_poison p (h.imp_right fun h => h.elim id False.elim), trivial⟩
  ubByOwnRules
    | .cons _ (.cons _ .nil), _, _, hub => nomatch hub

/-- `icmp` returns a result on two defined operands, with every
predicate. -/
theorem icmp_returnsOnDefined (p : Pred) (w : Nat) :
    ReturnsOnDefined (d := CoreDialect) (.icmp p w) := by
  refine ⟨.cons (.value 0) (.cons (.value 0) .nil), ?_, _, rfl⟩
  rintro (h | h | h) <;> cases h

/-- `icmp` has an outcome on every operand vector, with every predicate. -/
theorem icmp_total (p : Pred) (w : Nat) : OpTotal (d := CoreDialect) (.icmp p w) := fun
  | .cons _ (.cons _ .nil) => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `icmp` is monotone, with every predicate. -/
theorem icmp_monotone (p : Pred) (w : Nat) : OpMonotone (d := CoreDialect) (.icmp p w) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
    intro e he
    cases he
    exact ⟨_, rfl, icmpValues_isRefinedBy p ha hb, trivial⟩

/-! # `select` -/

/-- `select` on operands that refine others gives a value that refines
theirs: it chooses the same operand, or its condition was poison. -/
theorem selectValues_isRefinedBy {c c' : PoisonOr (BitVec 1)} {a b a' b' : PoisonOr (BitVec w)}
    (hc : c ⊑ c') (ha : a ⊑ a') (hb : b ⊑ b') : selectValues c a b ⊑ selectValues c' a' b' := by
  cases c with
  | poison => trivial
  | value x =>
    cases c' with
    | poison => exact hc.elim
    | value x' =>
      have hx : x = x' := hc
      subst hx
      show (if x = 1 then a else b) ⊑ (if x = 1 then a' else b')
      by_cases h1 : x = 1
      · rw [ite_eq_left h1, ite_eq_left h1]
        exact ha
      · rw [ite_eq_right h1, ite_eq_right h1]
        exact hb

/-- `select` has an outcome on every operand vector. -/
theorem select_total (w : Nat) : OpTotal (d := CoreDialect) (.select w) := fun
  | .cons _ (.cons _ (.cons _ .nil)) => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `select` is monotone. -/
theorem select_monotone (w : Nat) : OpMonotone (d := CoreDialect) (.select w) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons c (.cons a (.cons b .nil)), .cons c' (.cons a' (.cons b' .nil)), ⟨hc, ha, hb, _⟩ =>
    intro e he
    cases he
    exact ⟨_, rfl, selectValues_isRefinedBy hc ha hb, trivial⟩

end Fir.Core
