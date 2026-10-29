import Fir.Core.Signature
import Fir.Validation.Scope

/-!
The core dialect's part of validation: which core types are valid, which
symbols core ops refer to, and the rules of `ret` and `call`, which read the
op's context.

The width rules of each other op family, such as which widths `zext` may go
between, are added by the ticket that builds the family (#14 to #20). The
general rules of the previous sections already check every op's operand and
result types against its signature.
-/

namespace Fir.Core

/--
A core type is valid when it is `iN` with `N ≥ 1`. `i0` is not a type, and
`ptr` is reserved: M0 has no values of type `ptr`, because their meaning
waits for the memory model (S3).
-/
def Ty.Valid : Ty → Prop
  | .int w => 1 ≤ w
  | .ptr => False

/-- `call` refers to its callee's symbol; no other core op refers to one. -/
def Op.symbolRefs : Op → List String
  | .call f _ _ => [f]
  | _ => []

/--
The core rules that read an op's context.

* `ret` returns values of the function's result types.
* `call` passes and receives the types of its callee's signature.

For the other ops, the general rules are all there is so far. The ticket of
each op family adds the family's own rules here.
-/
def Op.Valid (ctx : OpContext CoreDialect) : Op → Prop
  | .ret ts => ts = ctx.results
  | .call f ts rs => ctx.symbols f = some ⟨ts, rs⟩
  | _ => True

end Fir.Core

namespace Fir

instance : DialectValidation CoreDialect where
  validTy := Core.Ty.Valid
  symbolRefs := Core.Op.symbolRefs
  validOp := Core.Op.Valid

end Fir
