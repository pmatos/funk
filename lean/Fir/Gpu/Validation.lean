import Fir.Gpu.Text
import Fir.Core.Validation
import Fir.Validation.Check

/-!
The rules of `gpu` (ADR-2026-11-09-1545). An op of `gpu` is valid when it
gives an `i32`, the width of every id and size of a work-item. It refers
to no symbol, and `gpu` adds no rule for a function, a region or an item:
whether a function is a kernel is where it lives, in a device module whose
dialect set names `gpu`, and the dialect-set rule already keeps every word
of `gpu` out of a module whose set does not name it.

The dialect accepts the core's valid types, since its types are the core's.
-/

namespace Fir.Gpu

/-- `gpu` accepts the core's valid types. -/
def ValidTy : Core.Ty ⊕ Empty → Prop
  | .inl t => t.Valid
  | .inr e => e.elim

instance instDecidableValidTy : DecidablePred ValidTy
  | .inl t => inferInstanceAs (Decidable t.Valid)
  | .inr e => e.elim

/-- The rule of an op of `gpu`: it gives an `i32`. -/
def Op.Valid : Op → Prop
  | .query _ _ w => w = 32

instance instDecidableOpValid : DecidablePred Op.Valid := fun o => by
  cases o <;> unfold Op.Valid <;> infer_instance

instance instDialectValidation : DialectValidation GpuDialect where
  validTy := ValidTy
  symbolRefs _ := []
  validOp _ := Op.Valid
  validFunc _ _ _ := True

instance instDecidableDialectValidation : DecidableDialectValidation GpuDialect where
  decValidTy t := inferInstanceAs (Decidable (ValidTy t))
  decValidOp _ o := inferInstanceAs (Decidable (Op.Valid o))
  decValidFunc _ _ _ := inferInstanceAs (Decidable True)

#guard decide (Op.Valid (.query .workItemId .x 32))
#guard !decide (Op.Valid (.query .workGroupSize .y 64))

end Fir.Gpu
