import Fir

/-!
Tests of the core dialect's effects, of the instance
`LawfulDialectEffects CoreDialect`, and the axioms of their proofs.

* _The instance._ It gives `udiv` at `i8` no poison on defined operands,
  `add` without flags no UB, and `freeze` no control.
* _Effects the core ops need._ For example, `add` with `nsw` and `shl` give
  poison on defined operands, `udiv` by zero, `cond_br` on poison and
  `unreachable` are UB, and `br` and `unreachable` are terminators:
  leaving any of those effects out of their sets would make the
  obligations false. `lean/FirTest/G0Effects.lean` pins every core op's
  set.
-/

namespace FirTest

open Fir Core

/-! # The instance -/

/-- The instance gives `udiv` at `i8` a defined result on defined operands. -/
theorem udiv8_makesNoPoison : MakesNoPoison (d := CoreDialect) (.udiv 8 false) :=
  LawfulDialectEffects.makesNoPoison _ (by unfold TypesValid; decide) (.inr rfl) rfl

/-- The instance gives `add` without flags no UB. -/
theorem add8_neverUB : NeverUB (d := CoreDialect) (.add 8 {}) :=
  LawfulDialectEffects.neverUB _ (by unfold TypesValid; decide) (.inr rfl) rfl

/-- `freeze` is not a terminator. -/
theorem freeze_notControl : Fir.isTerminator (d := CoreDialect) (.freeze 8) = false :=
  LawfulDialectEffects.notControl _ rfl

/-! # Effects the core ops need -/

/-- `add` with `nsw` gives poison on `127 + 1` at `i8`. -/
theorem addNsw_makesPoison : ¬ MakesNoPoison (d := CoreDialect) (.add 8 { nsw := true }) :=
  fun h => h rfl (.cons (.value 127) (.cons (.value 1) .nil)) (by rintro (h | h | h) <;> cases h) _
    rfl (.inl (show addWith (w := 8) { nsw := true } (.value 127) (.value 1) = .poison by decide))

/-- `shl` gives poison for a shift of `8` at `i8`. -/
theorem shl_makesPoison : ¬ MakesNoPoison (d := CoreDialect) (.shl 8) :=
  fun h => h rfl (.cons (.value 1) (.cons (.value 8) .nil)) (by rintro (h | h | h) <;> cases h) _
    rfl (.inl (show shlValues (w := 8) (.value 1) (.value 8) = .poison by decide))

/-- `udiv` by zero is UB. -/
theorem udiv_mayUB : ¬ NeverUB (d := CoreDialect) (.udiv 8 false) :=
  fun h => (h (.cons (.value 1) (.cons (.value 0) .nil)) _).1 rfl
    ((ruleOfEv_iff _ _ _ _).2 (.inr ⟨_, rfl, rfl⟩))

/-- `cond_br` on poison is UB. -/
theorem condBr_mayUB : ¬ NeverUB (d := CoreDialect) .condBr :=
  fun h => (h (.cons .poison .nil) _).2 rfl ((condBr_exit _ _).2 rfl)

/-- `br` is a terminator. -/
theorem br_control : Fir.isTerminator (d := CoreDialect) .br = true := rfl

/-- Reaching `unreachable` is UB. -/
theorem unreachable_mayUB : ¬ NeverUB (d := CoreDialect) .unreachable :=
  fun h => (h .nil _).2 rfl ((unreachable_exit _ _).2 rfl)

/-- `unreachable` is a terminator. -/
theorem unreachable_control : Fir.isTerminator (d := CoreDialect) .unreachable = true := rfl

/-! # The theorems' axioms -/

/-- info: 'Fir.Core.Op.neverUB_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.Op.neverUB_all

/-- info: 'Fir.Core.Op.makesNoPoison_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.Op.makesNoPoison_all

/-- info: 'Fir.Core.lawfulDialectEffects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.lawfulDialectEffects

end FirTest
