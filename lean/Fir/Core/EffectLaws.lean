import Fir.Core.Lawful
import Fir.Execution.MemoryObligationLaws
import Fir.Core.Unlawful

/-!
# The core dialect's effect obligations

The core dialect's effect declarations are sound: it is lawful in its
effects. Each effect that a core op leaves out, it does not have:

* _No may-UB._ Every core op but the four divisions, `cond_br` and
  `unreachable` never ends in UB. Each rule that gives a result gives it at once, `freeze`
  and the float arithmetic after choosing bits, and `br` and `ret` go to their successor or return.
* _No may produce poison._ On operands with no poison, every op that does
  not declare it gives a defined result: `add`, `sub` and `mul` without
  flags, the divisions without `exact` when they give a result, the bitwise
  ops, `icmp`, `fcmp`, `select`, the width changes, `const` at an integer
  and at a float type, `freeze`, and the float arithmetic, whose NaN
  results are defined bits.
* _No control._ Every core op that does not declare control is not a
  terminator.
* _No write, read or allocation._ No core op touches memory: it runs by its
  rule in the set monad and keeps the memories, at every naming of them
  (the section on meeting the memory obligations).

So the core's semantics with memory lifts its semantics in the set monad,
and the first two obligations, stated over the semantics with memory,
follow from what each rule does in the set monad.

`call` has no rule of its own, so the obligations leave it out: its meaning
is its callee's run, and its effects are its callee's
(ADR-2026-11-02-1514).

The obligations have teeth: the last section declares the core ops' effects
with `sdiv` left without may-UB, and shows that the obligations reject that
declaration, as the section on semantics that the obligations reject shows
for semantics.
-/

namespace Fir.Core

/-! # No may-UB -/

/-- Every core op that does not declare may-UB never ends in UB: each rule
gives its result, or its exit, at once. -/
theorem Op.neverUB_all : (op : Op) → (Fir.effects (d := CoreDialect) op).mayUB = false →
    NeverUBSetM (d := CoreDialect) op
  | .const .., _ | .fconst .., _ | .poison _, _ =>
    fun _ _ => ⟨fun _ h => (by cases h), fun h => nomatch h⟩
  | .add .., _ | .sub .., _ | .mul .., _ | .and _, _ | .or _, _ | .xor _, _ | .shl _, _
  | .lshr _, _ | .ashr _, _ | .icmp .., _ | .fcmp .., _ => fun
    | .cons _ (.cons _ .nil), _ => ⟨fun _ h => (by cases h), fun h => nomatch h⟩
  | .select _, _ => fun
    | .cons _ (.cons _ (.cons _ .nil)), _ => ⟨fun _ h => (by cases h), fun h => nomatch h⟩
  | .zext .., _ | .sext .., _ | .trunc .., _ => fun
    | .cons _ .nil, _ => ⟨fun _ h => (by cases h), fun h => nomatch h⟩
  | .freeze w, _ => fun
    | .cons a .nil, _ => ⟨fun _ h => (by
        obtain ⟨_, h, _⟩ := (freeze_denote w a _).1 h
        cases h), fun h => nomatch h⟩
  | .br, _ | .ret _, _ => fun _ _ => ⟨fun h => (nomatch h), fun _ h => (by cases h)⟩
  | .call .., _ => fun _ _ => ⟨fun _ h => h, fun h => nomatch h⟩
  | .fbin o e m, _ => fbin_neverUB o e m
  | .funary o e m, _ => funary_neverUB o e m
  | .fma e m, _ => fma_neverUB e m
  | .sdiv .., h | .udiv .., h | .srem _, h | .urem _, h | .condBr, h
  | .unreachable, h => nomatch h

/-! # No may produce poison -/

/-- An operand vector of one value with no poison holds a defined value. -/
theorem defined₁ {a : PoisonOr (BitVec w)}
    (h : ¬ (HVector.cons (f := toType) (as := []) (a := i w) a .nil).Any TyPoison.IsPoison) :
    ∃ x, a = .value x := by
  cases a with
  | poison => exact absurd (.inl rfl) h
  | value x => exact ⟨x, rfl⟩

/-- An operand vector of two values with no poison holds defined values. -/
theorem defined₂ {a : PoisonOr (BitVec w)} {b : PoisonOr (BitVec w')}
    (h : ¬ (HVector.cons (f := toType) (a := i w) a (.cons (a := i w') b .nil)).Any
      TyPoison.IsPoison) :
    ∃ x y, a = .value x ∧ b = .value y := by
  cases a with
  | poison => exact absurd (.inl rfl) h
  | value x =>
    cases b with
    | poison => exact absurd (.inr (.inl rfl)) h
    | value y => exact ⟨x, y, rfl, rfl⟩

/-- An operand vector of two floats with no poison holds defined values. -/
theorem defined₂Float {a b : PoisonOr (BitVec (floatWidth e m))}
    (h : ¬ (HVector.cons (f := toType) (a := Ty.float e m) a
      (.cons (a := Ty.float e m) b .nil)).Any TyPoison.IsPoison) :
    ∃ x y, a = .value x ∧ b = .value y := by
  cases a with
  | poison => exact absurd (.inl rfl) h
  | value x =>
    cases b with
    | poison => exact absurd (.inr (.inl rfl)) h
    | value y => exact ⟨x, y, rfl, rfl⟩

/-- A vector of one value that is not poison holds no poison. -/
theorem not_any_of_ne {v : PoisonOr (BitVec w)} (h : v ≠ .poison) :
    ¬ (HVector.cons (f := toType) (as := []) (a := i w) v .nil).Any TyPoison.IsPoison
  | .inl h' => h h'

/-- A vector of one float that is not poison holds no poison. -/
theorem not_any_of_ne_float {v : PoisonOr (BitVec (floatWidth e m))} (h : v ≠ .poison) :
    ¬ (HVector.cons (f := toType) (as := []) (a := Ty.float e m) v .nil).Any TyPoison.IsPoison
  | .inl h' => h h'

/-- On defined operands, the rule of a division whose quotient is defined
gives a defined result when it gives one. -/
theorem ruleOfEv_divEv_defined {q : BitVec w → BitVec w → PoisonOr (BitVec w)}
    (hq : ∀ x y, ∃ z, q x y = .value z) (x y : BitVec w) (rs : HVector toType [i w])
    (h : ruleOfEv (m := SetM) (divEv name signed q) (.cons (.value x) (.cons (.value y) .nil))
      (.ok rs)) : ¬ rs.Any TyPoison.IsPoison := by
  rcases (ruleOfEv_iff _ _ _ _).1 h with ⟨v, hv, he⟩ | ⟨_, _, he⟩
  · cases he
    rw [divEv.eq_3] at hv
    split at hv
    · cases hv
    · split at hv
      · cases hv
      · cases hv
        obtain ⟨z, hz⟩ := hq x y
        rw [hz]
        exact not_any_of_ne fun h => nomatch h
  · cases he

/-- A flag of `add`, `sub` or `mul` is the one way they may produce
poison: an instance that does not declare it has no flags. -/
theorem flags_none {f : WrapFlags} (h : (f != {}) = false) : f = {} := by
  simpa using h

/-- Every core op that does not declare that it may produce poison makes
none: on operands with no poison, it gives a defined result. -/
theorem Op.makesNoPoison_all : (op : Op) → (Fir.effects (d := CoreDialect) op).mayPoison = false →
    MakesNoPoisonSetM (d := CoreDialect) op
  | .const _ v, _ => fun _ _ _ _ h => by cases h; exact not_any_of_ne fun h => nomatch h
  | .fconst .., _ => fun _ _ _ _ h => by cases h; exact not_any_of_ne_float fun h => nomatch h
  | .fcmp .., _ => fun _ args hd _ hr => match args, hd, hr with
    | .cons _ (.cons _ .nil), hd, hr => by
      obtain ⟨x, y, rfl, rfl⟩ := defined₂Float hd
      cases hr
      exact not_any_of_ne fun h => nomatch h
  | .add _ f, h | .sub _ f, h | .mul _ f, h => by
    obtain rfl := flags_none h
    exact fun _ args hd _ hr => match args, hd, hr with
      | .cons _ (.cons _ .nil), hd, hr => by
        obtain ⟨x, y, rfl, rfl⟩ := defined₂ hd
        cases hr
        exact not_any_of_ne fun h => nomatch h
  | .and _, _ | .or _, _ | .xor _, _ | .icmp .., _ => fun _ args hd _ hr => match args, hd, hr with
    | .cons _ (.cons _ .nil), hd, hr => by
      obtain ⟨x, y, rfl, rfl⟩ := defined₂ hd
      cases hr
      exact not_any_of_ne fun h => nomatch h
  | .sdiv _ x, h | .udiv _ x, h => by
    cases (show x = false from h)
    exact fun _ args hd rs hr => match args, hd, hr with
      | .cons _ (.cons _ .nil), hd, hr => by
        obtain ⟨x, y, rfl, rfl⟩ := defined₂ hd
        exact ruleOfEv_divEv_defined (fun _ _ => ⟨_, ite_eq_right (by simp)⟩) x y rs hr
  | .srem _, _ | .urem _, _ => fun _ args hd rs hr => match args, hd, hr with
    | .cons _ (.cons _ .nil), hd, hr => by
      obtain ⟨x, y, rfl, rfl⟩ := defined₂ hd
      exact ruleOfEv_divEv_defined (fun _ _ => ⟨_, rfl⟩) x y rs hr
  | .select _, _ => fun _ args hd _ hr => match args, hd, hr with
    | .cons c (.cons a (.cons b .nil)), hd, hr => by
      cases c with
      | poison => exact absurd (.inl rfl) hd
      | value c =>
        obtain ⟨x, y, rfl, rfl⟩ := defined₂ fun h => hd (.inr h)
        cases hr
        refine not_any_of_ne ?_
        simp only [selectValues]
        split <;> simp
  | .zext .., _ | .sext .., _ | .trunc .., _ => fun _ args hd _ hr => match args, hd, hr with
    | .cons _ .nil, hd, hr => by
      obtain ⟨x, rfl⟩ := defined₁ hd
      cases hr
      exact not_any_of_ne fun h => nomatch h
  | .freeze w, _ => fun _ args _ _ hr => match args, hr with
    | .cons a .nil, hr => by
      obtain ⟨b, he, _⟩ := (freeze_denote w a _).1 hr
      cases he
      exact not_any_of_ne fun h => nomatch h
  | .call .., _ => fun _ _ _ _ hr => hr.elim
  | .fbin o e m, _ => fbin_makesNoPoison o e m
  | .funary o e m, _ => funary_makesNoPoison o e m
  | .fma e m, _ => fma_makesNoPoison e m
  | .br, _ | .condBr, _ | .ret _, _ | .unreachable, _ => fun h => nomatch h
  | .poison _, h | .shl _, h | .lshr _, h | .ashr _, h => nomatch h

/-! # No control -/

/-- Every core op that does not declare control is not a terminator. -/
theorem Op.notControl_all (op : Op) (h : (Fir.effects (d := CoreDialect) op).control = false) :
    Fir.isTerminator (d := CoreDialect) op = false := by
  cases op <;> first | rfl | exact nomatch h

end Fir.Core

namespace Fir

/-- No core op touches memory: at every naming of the core's memories, each
op runs by its rule in the set monad and keeps the memories. -/
instance Core.instDialectMemDenote : DialectMemDenote CoreDialect := DialectMemDenote.ofSetM

/-- The core dialect's semantics with memory lifts its semantics in the set
monad. -/
instance Core.liftsSetM : LiftsSetM CoreDialect := DialectMemDenote.ofSetM_liftsSetM

/-- The core dialect is lawful in its effects: every effect that a core op
leaves out, it does not have. -/
theorem Core.lawfulDialectEffects : LawfulDialectEffects CoreDialect where
  neverUB op _ _ h := NeverUB.ofSetM (Core.Op.neverUB_all op h)
  makesNoPoison op _ _ h := MakesNoPoison.ofSetM (Core.Op.makesNoPoison_all op h)
  notControl := Core.Op.notControl_all
  writesNot := DialectMemDenote.ofSetM_writesNot
  readsNot := DialectMemDenote.ofSetM_readsNot
  allocatesNot := DialectMemDenote.ofSetM_allocatesNot

instance : LawfulDialectEffects CoreDialect := Core.lawfulDialectEffects

/-! # A declaration that the obligations reject -/

namespace Core.Unlawful

/-- The core ops' effects, but `sdiv` declared without may-UB. -/
@[instance_reducible] def sdivNoUB : DialectEffects CoreDialect where
  Mem := Core.Mem
  poisonClass := Core.Op.poisonClass
  effects
    | .sdiv _ x => { mayPoison := x }
    | op => Core.Op.effects op

/-- `sdiv` by zero is UB, so the obligations reject the declaration: an op
left without may-UB must never end in UB. -/
theorem sdivNoUB_unlawful :
    ¬ @LawfulDialectEffects CoreDialect _ _ _ sdivNoUB _ _
      (@DialectMemDenote.ofSetM CoreDialect _ _ sdivNoUB _) := by
  intro h
  have hnever := @LawfulDialectEffects.neverUB CoreDialect _ _ _ sdivNoUB _ _ _ h
    (.sdiv 8 false) sdiv_typesValid (.inr rfl) rfl
  exact NoUB.of_lift ((hnever (N := Unit) (fun _ => 0) (fun _ => ())
    (.cons (.value 1) (.cons (.value 0) .nil))).1 rfl) Memory.Memories.empty _
    ((ruleOfEv_iff _ _ _ _).2 (.inr ⟨_, rfl, rfl⟩))

end Core.Unlawful

end Fir
