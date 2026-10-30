import Fir.Core.Signature
import Fir.Validation.Scope

/-!
The core dialect's part of validation: which core types are valid, which
symbols core ops refer to, the rules of `ret` and `call`, which read the
op's context, and the width rules of `zext`, `sext` and `trunc`
(ADR-2026-10-30-0818). The general rules of the previous sections already
check every op's operand and result types against its signature, so these
are all the rules of the core dialect.
-/

namespace Fir.Core

/--
A core type is valid when it is `iN` with `1 ≤ N ≤ maxWidth`. `i0` is not a
type, and `ptr` is reserved: M0 has no values of type `ptr`, because their
meaning waits for the memory model (S3).
-/
def Ty.Valid : Ty → Prop
  | .int w => 1 ≤ w ∧ w ≤ maxWidth
  | .ptr => False

/-- `call` refers to its callee's symbol; no other core op refers to one. -/
def Op.symbolRefs : Op → List String
  | .call f _ _ => [f]
  | _ => []

/--
The core rules of an op beyond its signature.

* `ret` returns values of the function's result types, any number of them.
* `call` passes and receives the types of its callee's signature, any
  number of each.
* `zext` and `sext` strictly widen, from `iM` to `iN` with `M < N`, and
  `trunc` strictly narrows, with `N < M`. A width change to the same width
  is not an op: the value itself is.

Every other op has no rule beyond its signature.
-/
def Op.Valid (ctx : OpContext CoreDialect) : Op → Prop
  | .ret ts => ts = ctx.results
  | .call f ts rs => ctx.symbols f = some ⟨ts, rs⟩
  | .zext m n | .sext m n => m < n
  | .trunc m n => n < m
  | _ => True

end Fir.Core

namespace Fir

instance : DialectValidation CoreDialect where
  validTy := Core.Ty.Valid
  symbolRefs := Core.Op.symbolRefs
  validOp := Core.Op.Valid

end Fir
