import Fir.Core.Lawful
import FirTest.RunsCalls

/-!
Tests of the instance `LawfulDialectPoison CoreDialect` and of the two
guards of the poison obligations, and the axioms of their proofs.

* _Valid op instances._ `udiv` at `i8` is one, so the instance gives it a
  result on defined operands. `udiv` at `i0` is not, and it has no such
  result (`Core.div_zero_width`): the guard is what lets the class hold.
  A `call` with a `ptr` operand is not one either, but a `call` with an
  `i8` result is.
* _Ops that run by their own rule._ `add` meets the guard, as an op with no
  callee, and `ret` as a terminator; `call` does not. In the set monad,
  `call` has no outcome, so it is not total at op level, even at a valid
  instance: the callee guard, not validity, is what lets the class leave
  it out.
* _Generic theorems for the core dialect._ Every op of a valid module with
  recursion and mutual recursion is a valid op instance, and `@even`, which
  calls `@odd`, which calls it back, has an outcome at every budget by the
  lawful class alone (`Func.progress_of_lawful`). The sum of the core
  dialect and a lawful extension is lawful, as `FirTest.LawfulRefine`
  shows with the spec's `Dialect.sum.lawfulPoison`.
-/

namespace FirTest

open Fir Core Example

/-! # Valid op instances -/

/-- `udiv` at `i8` is a valid op instance. -/
theorem udiv8_typesValid : TypesValid (d := CoreDialect) (.udiv 8 false) := by
  unfold TypesValid; decide

/-- `udiv` at `i0` is not: validation rejects `i0`. -/
theorem udiv0_not_typesValid : ¬ TypesValid (d := CoreDialect) (.udiv 0 false) := by
  unfold TypesValid; decide

/-- A `call` with a `ptr` operand is not: validation rejects `ptr`. -/
theorem callPtr_not_typesValid : ¬ TypesValid (d := CoreDialect) (.call "f" [.ptr] []) := by
  unfold TypesValid; decide

/-- A `call` with an `i8` result is a valid op instance, so validity alone
does not leave `call` out of the obligations. -/
theorem call_typesValid : TypesValid (d := CoreDialect) (.call "f" [] [i 8]) := by
  unfold TypesValid; decide

/-- The instance gives `udiv` at `i8` a result on defined operands. -/
theorem udiv8_returnsOnDefined : ReturnsOnDefined (d := CoreDialect) (.udiv 8 false) :=
  LawfulDialectPoison.returnsOnDefined _ udiv8_typesValid rfl

/-- `udiv` at `i0` has none: every divisor is zero. -/
theorem udiv0_noResult : ¬ ReturnsOnDefined (d := CoreDialect) (.udiv 0 false) :=
  (div_zero_width false).2.1

/-! # Ops that run by their own rule -/

/-- `add` runs by its own rule: it calls no function. -/
theorem add_byRule :
    isTerminator (d := CoreDialect) (.add 8 {}) = true ∨
      callee? (d := CoreDialect) (.add 8 {}) = none :=
  .inr rfl

/-- `ret` runs by its own rule: it is a terminator. -/
theorem ret_byRule :
    isTerminator (d := CoreDialect) (.ret [i 8]) = true ∨
      callee? (d := CoreDialect) (.ret [i 8]) = none :=
  .inl rfl

/-- `call` does not: it runs its callee. -/
theorem call_not_byRule :
    ¬ (isTerminator (d := CoreDialect) (.call "f" [] [i 8]) = true ∨
      callee? (d := CoreDialect) (.call "f" [] [i 8]) = none) := by
  decide

/-- In the set monad, `call` has no outcome: it has no rule at op level. -/
theorem call_noOutcome (args : HVector toType [i 8]) (e : Ev (HVector toType [i 8])) :
    ¬ DialectDenote.denote (m := SetM) (d := CoreDialect) (.call "f" [i 8] [i 8]) args e :=
  fun h => h

/-- So `call` is not total at op level, at a valid instance
(`call_typesValid`): an unguarded `total` would be false, and the class
does not ask it. -/
theorem call_not_total : ¬ OpTotal (d := CoreDialect) (.call "f" [] [i 8]) := fun h => by
  obtain ⟨_, he⟩ := (h .nil).1 rfl
  exact he

/-- The instance gives totality and monotonicity of `udiv` at `i8`. -/
theorem udiv8_total_monotone :
    OpTotal (d := CoreDialect) (.udiv 8 false) ∧ OpMonotone (d := CoreDialect) (.udiv 8 false) :=
  ⟨LawfulDialectPoison.total _ udiv8_typesValid (.inr rfl),
    LawfulDialectPoison.monotone _ udiv8_typesValid (.inr rfl)⟩

/-! # Generic theorems for the core dialect -/

/-- Every op of the module of `@fact`, `@even` and `@odd` is a valid op
instance. -/
theorem recModule_typesValid :
    ∀ g ∈ recModule.funcs, ∀ b ∈ g.blocks, ∀ o ∈ b.body, TypesValid o.op :=
  fun g hg _ hb _ ho => (recModule_valid.funcs g hg).typesValid hb ho

/-- A run of `@even`, which calls `@odd`, which calls it back, has an
outcome at every budget, by the lawful class alone. -/
theorem even_progress_of_lawful (args : HVector toType (evenFn.params.map (·.2))) :
    Progress (funcRuns recModule evenFn args) :=
  Func.progress_of_lawful recModule_valid.funcs
    (fun g hg => inModule_of_valid (recModule_valid.funcs g hg))
    (by simp [recModule, Module.funcs]) args

/-! # Axioms -/

/-- info: 'Fir.Func.Valid.typesValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.Valid.typesValid

/-- info: 'Fir.Func.progress_of_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.progress_of_lawful

/-- info: 'Fir.Core.Op.propagates_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.Op.propagates_all

/-- info: 'Fir.Core.pos_of_typesValid' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.pos_of_typesValid

/-- info: 'Fir.Core.Op.returnsOnDefined_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.Op.returnsOnDefined_valid

/-- info: 'Fir.Core.lawfulDialectPoison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.lawfulDialectPoison

/-- info: 'Fir.Core.Unlawful.add_typesValid' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.Unlawful.add_typesValid

/-- info: 'Fir.Core.Unlawful.sdiv_typesValid' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.Unlawful.sdiv_typesValid

/-- info: 'FirTest.udiv8_typesValid' depends on axioms: [propext] -/
#guard_msgs in #print axioms FirTest.udiv8_typesValid

/-- info: 'FirTest.udiv0_not_typesValid' depends on axioms: [propext] -/
#guard_msgs in #print axioms FirTest.udiv0_not_typesValid

/-- info: 'FirTest.callPtr_not_typesValid' depends on axioms: [propext] -/
#guard_msgs in #print axioms FirTest.callPtr_not_typesValid

/-- info: 'FirTest.call_typesValid' depends on axioms: [propext] -/
#guard_msgs in #print axioms FirTest.call_typesValid

/-- info: 'FirTest.udiv8_returnsOnDefined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.udiv8_returnsOnDefined

/-- info: 'FirTest.udiv0_noResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.udiv0_noResult

/-- info: 'FirTest.add_byRule' depends on axioms: [propext] -/
#guard_msgs in #print axioms FirTest.add_byRule

/-- info: 'FirTest.ret_byRule' depends on axioms: [propext] -/
#guard_msgs in #print axioms FirTest.ret_byRule

/-- info: 'FirTest.call_not_byRule' depends on axioms: [propext] -/
#guard_msgs in #print axioms FirTest.call_not_byRule

/-- info: 'FirTest.call_noOutcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.call_noOutcome

/-- info: 'FirTest.call_not_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.call_not_total

/-- info: 'FirTest.udiv8_total_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.udiv8_total_monotone

/-- info: 'FirTest.recModule_typesValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.recModule_typesValid

/-- info: 'FirTest.even_progress_of_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.even_progress_of_lawful

/-- info: 'Fir.Core.Unlawful.noOutcome_unlawful' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.Unlawful.noOutcome_unlawful

/-- info: 'Fir.Core.Unlawful.poisonIsUB_unlawful' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.Unlawful.poisonIsUB_unlawful

/-- info: 'Fir.Core.Unlawful.oldSDiv_unlawful' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.Unlawful.oldSDiv_unlawful

/-- info: 'Fir.Core.Unlawful.alwaysUB_unlawful' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.Unlawful.alwaysUB_unlawful

end FirTest
