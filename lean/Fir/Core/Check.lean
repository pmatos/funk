import Fir.Core.Rejects
import Fir.Validation.CheckModule

/-!
The validation check needs a dialect's types to have decidable equality, and
its two rules to be decidable. The core dialect's types derive
`DecidableEq`, and its rules are decided below, case by case. With them,
the check covers every one of the 24 core ops: the general rules check each
op's operand and result types, its place in its block, its successors and
its uses against its signature, and `Op.Valid` adds the rules of `ret`,
`call`, `zext`, `sext` and `trunc`.
-/

namespace Fir.Core

instance : DecidablePred Ty.Valid := fun t => by
  cases t <;> unfold Ty.Valid <;> infer_instance

instance (ctx : OpContext CoreDialect) : DecidablePred (Op.Valid ctx) := fun o => by
  cases o <;> unfold Op.Valid <;> infer_instance

end Fir.Core

namespace Fir

instance : DecidableDialectValidation CoreDialect where
  decValidTy t := inferInstanceAs (Decidable (Core.Ty.Valid t))
  decValidOp ctx o := inferInstanceAs (Decidable (Core.Op.Valid ctx o))

end Fir

/-!
# The rejected function, checked

The check finds a problem in the function `deadBlock` of the previous
section, in any module, since it decides validation and validation rejects
that function. Its one problem names the block that the entry does not
reach, `^dead`.
-/

namespace Fir.Core.Rejects

/-- The check finds a problem in `deadBlock`, in any module. -/
theorem deadBlock_problems {lk : Lookup CoreDialect} {ctx : ModuleContext CoreDialect}
    (h : lk.Agrees ctx) : deadBlock.problems lk ≠ [] :=
  fun e => deadBlock_rejected ctx ((Func.problems_eq_nil h).mp e)

/-- `deadBlock` alone in a module whose location table has `@0`. -/
def deadModule : Module CoreDialect := ⟨[.func deadBlock], [(0, .unknown)]⟩

#guard deadModule.problems ==
  [{ message := "block ^dead is not reachable from the entry", func := some "f",
     block := some "dead", loc := some 0 }]

end Fir.Core.Rejects
