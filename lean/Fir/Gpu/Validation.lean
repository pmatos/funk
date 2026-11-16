import Fir.Gpu.Text
import Fir.Core.Validation
import Fir.Validation.Check

/-!
The rules of `gpu` (ADR-2026-11-09-1545). A question of `gpu` is valid
when it gives an `i32`, the width of every id and size of a work-item.
`gpu.work_group_alloca` has the rules of `alloca` but its kind: it
allocates at least one value, aligned to a power of two of units no larger
than `MemLayout.limit`, and its type is a valid integer or pointer type.
Its result names its memory, and a pointer type that it allocates values of
names one too (`Op.attrTypes`), so the module's data layout checks that the
module has each, as for `alloca`: work-group memory is any memory that the
host's data layout declares (the human's ruling of 2026-11-16 on #212). No
op of `gpu` refers to a symbol, and `gpu` adds no rule for a function, a region or an item:
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

/-- The rule of an op of `gpu`: a question gives an `i32`, and an
allocation has the rules of `alloca` but its kind. -/
def Op.Valid : Op → Prop
  | .query _ _ w => w = 32
  | .alloc t c a _ => 1 ≤ c ∧ (∀ x ∈ a, MemLayout.ValidAlign x) ∧ t.IsElem ∧ t.Valid

/-- The type that an allocation in work-group memory allocates values of,
which it carries in its attributes, so that the data layout checks the
memory that a pointer type there names, as for `alloca`
(`Core.Op.attrTypes`). -/
def Op.attrTypes : Op → List (Core.Ty ⊕ Empty)
  | .alloc t _ _ _ => if t.Valid then [.inl t] else []
  | .query .. => []

instance instDecidableOpValid : DecidablePred Op.Valid := fun o => by
  cases o <;> unfold Op.Valid <;> infer_instance

instance instDialectValidation : DialectValidation GpuDialect where
  validTy := ValidTy
  symbolRefs _ := []
  validOp _ := Op.Valid
  validFunc _ _ _ := True
  opTypes := Op.attrTypes

instance instDecidableDialectValidation : DecidableDialectValidation GpuDialect where
  decValidTy t := inferInstanceAs (Decidable (ValidTy t))
  decValidOp _ o := inferInstanceAs (Decidable (Op.Valid o))
  decValidFunc _ _ _ := inferInstanceAs (Decidable True)

#guard decide (Op.Valid (.query .workItemId .x 32))
#guard !decide (Op.Valid (.query .workGroupSize .y 64))
#guard decide (Op.Valid (.alloc (.int 32) 64 (some 4) 3))
#guard decide (Op.Valid (.alloc (.ptr 5) 1 none 3))
#guard !decide (Op.Valid (.alloc (.int 32) 0 none 3))
#guard !decide (Op.Valid (.alloc (.int 32) 1 (some 3) 3))
#guard !decide (Op.Valid (.alloc (.float 8 23) 1 none 3))

end Fir.Gpu
