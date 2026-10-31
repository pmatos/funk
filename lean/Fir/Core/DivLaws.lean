import Fir.Core.Semantics
import Fir.Core.Poison

/-!
# Division and remainder are lawful

`sdiv`, `udiv`, `srem` and `urem`, with and without `exact`, meet the
obligations of the poison classes section. They propagate poison
(ADR-2026-10-30-0818), so each meets both poison clauses, returns a result
on some operands with no poison, and is total and monotone:

* _Poison out._ On a poison operand, a division is UB or gives poison,
  whatever `exact` says: `exact` is checked only on two values.
* _UB only by the op's own rules._ A division is UB on a poison divisor,
  and a zero divisor in its place is UB too. It is UB on a poison dividend
  only when the divisor is zero, or when the op is signed and the divisor
  is `-1`; then the signed minimum in its place is UB too.
* _Totality._ A division ends in exactly one way on every two operands:
  with a result or with UB.
* _Monotonicity._ A defined value is refined only by itself, so only a
  poison operand can be refined to something else. A poison divisor is UB,
  which allows anything. A poison dividend by a divisor that makes it UB
  allows anything too. By any other divisor it gives poison, which every
  result refines, and the refined dividend, poison or a value, gives a
  result there, never UB. This is the case that the rejected rule broke
  (`Core.Unlawful.oldSDiv_unlawful`).

The proofs are about `divEv`, once for the four ops, with any name, any
signedness and any result on two values, so they hold with and without
`exact`. `ruleOfEv` carries them to each op's semantics.

# A width of zero

`i0` is not a type: validation rejects it. The obligations, though, speak
of every op instance, `udiv 0 false` among them. `BitVec 0` has one value,
`0`, so at width zero every divisor is zero and every division is UB.
No division at width zero returns a result on defined operands, as
`div_zero_width` shows. So the four ops return a result on defined
operands at every width above zero, and only there. The lawful class
`LawfulDialectPoison` asks it of every op instance that propagates poison,
`i0` ones included, so the core dialect cannot meet that class as it is
stated. Either the rule for a zero divisor or the class has to change at
width zero; which one is pending the human's decision in #69.
-/

namespace Fir.Core

variable {w : Nat} {name : String} {signed : Bool} {q : BitVec w → BitVec w → PoisonOr (BitVec w)}

/-! # The rule of the four ops -/

/-- On a poison operand, a division that gives a result gives poison. -/
theorem divEv_poison {a b r : PoisonOr (BitVec w)} (h : a = .poison ∨ b = .poison)
    (hr : divEv name signed q a b = .ok r) : r = .poison := by
  rcases h with rfl | rfl
  · cases b with
    | poison => rw [divEv.eq_1] at hr; cases hr
    | value y =>
      rw [divEv.eq_2] at hr
      split at hr
      · cases hr
      · split at hr
        · cases hr
        · cases hr; rfl
  · rw [divEv.eq_1] at hr; cases hr

/-- On a poison operand, a division that is UB is UB on some values in
place of each poison: a zero divisor, or the signed minimum divided by
`-1`. -/
theorem divEv_fill {a b : PoisonOr (BitVec w)} {r : String} (h : a = .poison ∨ b = .poison)
    (hr : divEv name signed q a b = .ub r) :
    ∃ x y, (a = .poison ∨ a = .value x) ∧ (b = .poison ∨ b = .value y) ∧
      ∃ r', divEv name signed q (.value x) (.value y) = .ub r' := by
  cases b with
  | poison =>
    refine ⟨match a with | .poison => 0 | .value x => x, 0, ?_, .inl rfl, ?_⟩
    · cases a
      · exact .inl rfl
      · exact .inr rfl
    · rw [divEv.eq_3]
      exact ⟨_, ite_eq_left rfl⟩
  | value y =>
    have ha : a = .poison := h.resolve_right (fun h => nomatch h)
    subst ha
    refine ⟨BitVec.intMin w, y, .inl rfl, .inr rfl, ?_⟩
    rw [divEv.eq_2] at hr
    rw [divEv.eq_3]
    by_cases hy : y = 0
    · exact ⟨_, ite_eq_left hy⟩
    · rw [ite_eq_right hy] at hr
      rw [ite_eq_right hy]
      by_cases hs : signed ∧ y = -1
      · exact ⟨_, ite_eq_left ⟨hs.1, rfl, hs.2⟩⟩
      · rw [ite_eq_right hs] at hr
        cases hr

/-- One way to end refines itself. -/
theorem _root_.Fir.Ev.isRefinedBy_refl {r : α → α → Prop} (hr : ∀ a, r a a) :
    ∀ e : Ev α, Ev.IsRefinedBy r e e
  | .ok a => hr a
  | .ub _ => trivial

/-- On operands that refine others, a division ends in a way that the
division of the others allows. -/
theorem divEv_isRefinedBy {a b a' b' : PoisonOr (BitVec w)} (ha : a ⊑ a') (hb : b ⊑ b') :
    Ev.IsRefinedBy (· ⊑ ·) (divEv name signed q a b) (divEv name signed q a' b') := by
  cases b with
  | poison => rw [divEv.eq_1]; trivial
  | value y =>
    cases b' with
    | poison => exact hb.elim
    | value y' =>
      have hy : y = y' := hb
      subst hy
      cases a with
      | value x =>
        cases a' with
        | poison => exact ha.elim
        | value x' =>
          have hx : x = x' := ha
          subst hx
          exact Ev.isRefinedBy_refl PoisonOr.isRefinedBy_refl _
      | poison =>
        rw [divEv.eq_2]
        by_cases hy : y = 0
        · rw [ite_eq_left hy]
          trivial
        · rw [ite_eq_right hy]
          by_cases hs : signed ∧ y = -1
          · rw [ite_eq_left hs]
            trivial
          · rw [ite_eq_right hs]
            cases a' with
            | poison =>
              rw [divEv.eq_2, ite_eq_right hy, ite_eq_right hs]
              trivial
            | value x' =>
              rw [divEv.eq_3, ite_eq_right hy, ite_eq_right fun h => hs ⟨h.1, h.2.2⟩]
              trivial

/-- At a width above zero, a division of `0` by `1` gives a result. -/
theorem divEv_zero_one (hw : 0 < w) :
    divEv name signed q (.value 0) (.value 1) = .ok (q 0 1) := by
  have h1 : (1 : BitVec w) ≠ 0 := fun h => by
    have := congrArg BitVec.toNat h
    simp at this
    omega
  have h2 : ¬ (signed ∧ (0 : BitVec w) = BitVec.intMin w ∧ (1 : BitVec w) = -1) :=
    fun h => by
      have := BitVec.intMin_eq_zero_iff.1 h.2.1.symm
      omega
  rw [divEv.eq_3, ite_eq_right h1, ite_eq_right h2]

/-- At width zero, a division by any value is UB: the divisor is zero. -/
theorem divEv_width_zero {q₀ : BitVec 0 → BitVec 0 → PoisonOr (BitVec 0)}
    (a : PoisonOr (BitVec 0)) (y : BitVec 0) : ∃ r, divEv name signed q₀ a (.value y) = .ub r := by
  have hy : y = 0 := BitVec.of_length_zero
  cases a
  · rw [divEv.eq_2]
    exact ⟨_, ite_eq_left hy⟩
  · rw [divEv.eq_3]
    exact ⟨_, ite_eq_left hy⟩

/-! # The rule of each op -/

/-- In the set monad, `ruleOfEv g` ends on `a` and `b` as `g a b` says. -/
theorem ruleOfEv_iff (g : PoisonOr (BitVec w) → PoisonOr (BitVec w) → Ev (PoisonOr (BitVec w)))
    (a b : PoisonOr (BitVec w)) (e : Ev (HVector toType [i w])) :
    ruleOfEv (m := SetM) g (.cons a (.cons b .nil)) e ↔
      (∃ v, g a b = .ok v ∧ e = .ok (.cons v .nil)) ∨ (∃ r, g a b = .ub r ∧ e = .ub r) := by
  have h : ruleOfEv (m := SetM) g (.cons a (.cons b .nil)) =
      match g a b with
      | .ok v => pure (.cons v .nil)
      | .ub r => MonadUB.ub r := rfl
  rw [h]
  cases g a b with
  | ok v =>
    exact ⟨fun h => .inl ⟨v, rfl, h⟩, fun
      | .inl ⟨_, hv, he⟩ => by cases hv; exact he
      | .inr ⟨_, hv, _⟩ => nomatch hv⟩
  | ub r =>
    exact ⟨fun h => .inr ⟨r, rfl, h⟩, fun
      | .inl ⟨_, hv, _⟩ => nomatch hv
      | .inr ⟨_, hv, he⟩ => by cases hv; exact he⟩

/-- A rule made by `ruleOfEv` has an outcome on every operand vector. -/
theorem ruleOfEv_total (g : PoisonOr (BitVec w) → PoisonOr (BitVec w) → Ev (PoisonOr (BitVec w))) :
    ∀ args : HVector toType [i w, i w], ∃ e, ruleOfEv (m := SetM) g args e
  | .cons a (.cons b .nil) => match h : g a b with
    | .ok v => ⟨_, (ruleOfEv_iff g a b _).2 (.inl ⟨v, h, rfl⟩)⟩
    | .ub r => ⟨_, (ruleOfEv_iff g a b _).2 (.inr ⟨r, h, rfl⟩)⟩

/-- Poison out, for a division. -/
theorem div_poisonOut :
    ∀ args : HVector toType [i w, i w], args.Any TyPoison.IsPoison →
      ∀ rs, ruleOfEv (m := SetM) (divEv name signed q) args (.ok rs) → rs.All TyPoison.IsPoison
  | .cons a (.cons b .nil), h, _, hrs => by
    rcases (ruleOfEv_iff _ a b _).1 hrs with ⟨v, hv, he⟩ | ⟨_, _, he⟩
    · cases he
      exact ⟨divEv_poison (h.imp_right fun h => h.elim id False.elim) hv, trivial⟩
    · cases he

/-- UB only by the op's own rules, for a division. -/
theorem div_ubByOwnRules :
    ∀ (args : HVector toType [i w, i w]) (r : String), args.Any TyPoison.IsPoison →
      ruleOfEv (m := SetM) (divEv name signed q) args (.ub r) →
      ∃ args', args.IsFilledBy (d := CoreDialect) args' ∧
        ∃ r', ruleOfEv (m := SetM) (divEv name signed q) args' (.ub r')
  | .cons a (.cons b .nil), _, h, hub => by
    rcases (ruleOfEv_iff _ a b _).1 hub with ⟨_, _, he⟩ | ⟨_, hr, he⟩
    · cases he
    · cases he
      obtain ⟨x, y, hx, hy, r', hr'⟩ := divEv_fill (h.imp_right fun h => h.elim id False.elim) hr
      refine ⟨.cons (.value x) (.cons (.value y) .nil), ⟨?_, hx, hy, trivial⟩, _,
        (ruleOfEv_iff _ _ _ _).2 (.inr ⟨r', hr', rfl⟩)⟩
      rintro (h | h | h) <;> cases h

/-- A division returns a result on two defined operands, at a width above
zero. -/
theorem div_returnsOnDefined (hw : 0 < w) :
    ∃ args : HVector toType [i w, i w], ¬ args.Any TyPoison.IsPoison ∧
      ∃ rs, ruleOfEv (m := SetM) (divEv name signed q) args (.ok rs) := by
  refine ⟨.cons (.value 0) (.cons (.value 1) .nil), ?_, _,
    (ruleOfEv_iff _ _ _ _).2 (.inl ⟨_, divEv_zero_one hw, rfl⟩)⟩
  rintro (h | h | h) <;> cases h

/-- At width zero, a division returns no result on defined operands: it
is UB. -/
theorem div_width_zero_noResult {q₀ : BitVec 0 → BitVec 0 → PoisonOr (BitVec 0)} :
    ∀ args : HVector toType [i 0, i 0], ¬ args.Any TyPoison.IsPoison →
      ∀ rs, ¬ ruleOfEv (m := SetM) (divEv name signed q₀) args (.ok rs)
  | .cons a (.cons b .nil), hn, _, hrs => by
    cases b with
    | poison => exact hn (.inr (.inl rfl))
    | value y =>
      obtain ⟨r, hr⟩ := divEv_width_zero (name := name) (signed := signed) (q₀ := q₀) a y
      rcases (ruleOfEv_iff _ a _ _).1 hrs with ⟨_, hv, _⟩ | ⟨_, _, he⟩
      · rw [hr] at hv
        cases hv
      · cases he

/-- A division is monotone. -/
theorem div_monotone (args args' : HVector toType [i w, i w])
    (h : args.Forall₂ TyRefinement.IsRefinedBy args') :
    SetM.IsRefinedBy (HVector.Forall₂ TyRefinement.IsRefinedBy)
      (ruleOfEv (divEv name signed q) args) (ruleOfEv (divEv name signed q) args') := by
  match args, args', h with
  | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
    intro e he
    have hr := divEv_isRefinedBy (name := name) (signed := signed) (q := q) ha hb
    rcases (ruleOfEv_iff _ a' b' e).1 he with ⟨v', hv', rfl⟩ | ⟨r', hr', rfl⟩
    · rw [hv'] at hr
      match hd : divEv name signed q a b, hr with
      | .ok v, hr => exact ⟨_, (ruleOfEv_iff _ a b _).2 (.inl ⟨v, hd, rfl⟩), hr, trivial⟩
      | .ub r, _ => exact ⟨_, (ruleOfEv_iff _ a b _).2 (.inr ⟨r, hd, rfl⟩), trivial⟩
    · rw [hr'] at hr
      match hd : divEv name signed q a b, hr with
      | .ok _, hr => exact hr.elim
      | .ub r, _ => exact ⟨_, (ruleOfEv_iff _ a b _).2 (.inr ⟨r, hd, rfl⟩), trivial⟩

/-! # `sdiv`, `udiv`, `srem` and `urem` -/

-- The four ops have rules, with and without `exact`.
#guard [true, false].all fun x =>
  (Op.sdiv 1 x).hasRules && (Op.udiv 64 x).hasRules && (Op.srem 7).hasRules && (Op.urem 33).hasRules

/-- `sdiv` propagates poison, with or without `exact`. -/
theorem sdiv_propagatesPoison (w : Nat) (x : Bool) :
    PropagatesPoison (d := CoreDialect) (.sdiv w x) where
  poisonOut := div_poisonOut
  ubByOwnRules := div_ubByOwnRules

/-- `sdiv` returns a result on two defined operands, at a width above
zero, with or without `exact`. -/
theorem sdiv_returnsOnDefined (w : Nat) (hw : 0 < w) (x : Bool) :
    ReturnsOnDefined (d := CoreDialect) (.sdiv w x) :=
  div_returnsOnDefined hw

/-- `sdiv` has an outcome on every operand vector, with or without `exact`. -/
theorem sdiv_total (w : Nat) (x : Bool) : OpTotal (d := CoreDialect) (.sdiv w x) := fun args =>
  ⟨fun _ => ruleOfEv_total _ args, fun h => nomatch h⟩

/-- `sdiv` is monotone, with or without `exact`. -/
theorem sdiv_monotone (w : Nat) (x : Bool) : OpMonotone (d := CoreDialect) (.sdiv w x) :=
  fun args args' h => ⟨fun _ => div_monotone args args' h, fun h => nomatch h⟩

/-- `udiv` propagates poison, with or without `exact`. -/
theorem udiv_propagatesPoison (w : Nat) (x : Bool) :
    PropagatesPoison (d := CoreDialect) (.udiv w x) where
  poisonOut := div_poisonOut
  ubByOwnRules := div_ubByOwnRules

/-- `udiv` returns a result on two defined operands, at a width above
zero, with or without `exact`. -/
theorem udiv_returnsOnDefined (w : Nat) (hw : 0 < w) (x : Bool) :
    ReturnsOnDefined (d := CoreDialect) (.udiv w x) :=
  div_returnsOnDefined hw

/-- `udiv` has an outcome on every operand vector, with or without `exact`. -/
theorem udiv_total (w : Nat) (x : Bool) : OpTotal (d := CoreDialect) (.udiv w x) := fun args =>
  ⟨fun _ => ruleOfEv_total _ args, fun h => nomatch h⟩

/-- `udiv` is monotone, with or without `exact`. -/
theorem udiv_monotone (w : Nat) (x : Bool) : OpMonotone (d := CoreDialect) (.udiv w x) :=
  fun args args' h => ⟨fun _ => div_monotone args args' h, fun h => nomatch h⟩

/-- `srem` propagates poison. -/
theorem srem_propagatesPoison (w : Nat) :
    PropagatesPoison (d := CoreDialect) (.srem w) where
  poisonOut := div_poisonOut
  ubByOwnRules := div_ubByOwnRules

/-- `srem` returns a result on two defined operands, at a width above
zero. -/
theorem srem_returnsOnDefined (w : Nat) (hw : 0 < w) :
    ReturnsOnDefined (d := CoreDialect) (.srem w) :=
  div_returnsOnDefined hw

/-- `srem` has an outcome on every operand vector. -/
theorem srem_total (w : Nat) : OpTotal (d := CoreDialect) (.srem w) := fun args =>
  ⟨fun _ => ruleOfEv_total _ args, fun h => nomatch h⟩

/-- `srem` is monotone. -/
theorem srem_monotone (w : Nat) : OpMonotone (d := CoreDialect) (.srem w) :=
  fun args args' h => ⟨fun _ => div_monotone args args' h, fun h => nomatch h⟩

/-- `urem` propagates poison. -/
theorem urem_propagatesPoison (w : Nat) :
    PropagatesPoison (d := CoreDialect) (.urem w) where
  poisonOut := div_poisonOut
  ubByOwnRules := div_ubByOwnRules

/-- `urem` returns a result on two defined operands, at a width above
zero. -/
theorem urem_returnsOnDefined (w : Nat) (hw : 0 < w) :
    ReturnsOnDefined (d := CoreDialect) (.urem w) :=
  div_returnsOnDefined hw

/-- `urem` has an outcome on every operand vector. -/
theorem urem_total (w : Nat) : OpTotal (d := CoreDialect) (.urem w) := fun args =>
  ⟨fun _ => ruleOfEv_total _ args, fun h => nomatch h⟩

/-- `urem` is monotone. -/
theorem urem_monotone (w : Nat) : OpMonotone (d := CoreDialect) (.urem w) :=
  fun args args' h => ⟨fun _ => div_monotone args args' h, fun h => nomatch h⟩

/-- At width zero, no division returns a result on defined operands, with
or without `exact`: every divisor is zero. -/
theorem div_zero_width (x : Bool) :
    ¬ ReturnsOnDefined (d := CoreDialect) (.sdiv 0 x) ∧
      ¬ ReturnsOnDefined (d := CoreDialect) (.udiv 0 x) ∧
      ¬ ReturnsOnDefined (d := CoreDialect) (.srem 0) ∧
      ¬ ReturnsOnDefined (d := CoreDialect) (.urem 0) :=
  ⟨fun ⟨args, hn, _, hrs⟩ => div_width_zero_noResult args hn _ hrs,
    fun ⟨args, hn, _, hrs⟩ => div_width_zero_noResult args hn _ hrs,
    fun ⟨args, hn, _, hrs⟩ => div_width_zero_noResult args hn _ hrs,
    fun ⟨args, hn, _, hrs⟩ => div_width_zero_noResult args hn _ hrs⟩

end Fir.Core
