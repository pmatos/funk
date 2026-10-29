import Fir.Core.Ops

/-!
The core dialect is the first instance of the dialect classes. Its signature
gives the operand and result types of every M0 op, and says which ops end a
block and how many successors they have.
-/

namespace Fir

/-- The core dialect: the M0 op instances and the M0 types. -/
abbrev CoreDialect : Dialect := ⟨Core.Op, Core.Ty⟩

namespace Core

/-- `iN` with `N = w`. -/
abbrev i (w : Nat) : Ty := .int w

/-- The operand types of each core op. -/
def Op.sig : Op → List Ty
  | .const _ _ | .br => []
  | .add w _ | .sub w _ | .mul w _ | .sdiv w _ | .udiv w _ | .srem w | .urem w
  | .and w | .or w | .xor w | .shl w | .lshr w | .ashr w | .icmp _ w => [i w, i w]
  | .select w => [i 1, i w, i w]
  | .zext m _ | .sext m _ | .trunc m _ => [i m]
  | .freeze w => [i w]
  | .condBr => [i 1]
  | .ret ts => ts
  | .call _ ts _ => ts

/-- The result types of each core op. -/
def Op.returnTypes : Op → List Ty
  | .const w _ | .add w _ | .sub w _ | .mul w _ | .sdiv w _ | .udiv w _
  | .srem w | .urem w | .and w | .or w | .xor w | .shl w | .lshr w | .ashr w
  | .select w | .freeze w => [i w]
  | .icmp _ _ => [i 1]
  | .zext _ n | .sext _ n | .trunc _ n => [i n]
  | .br | .condBr | .ret _ => []
  | .call _ _ rs => rs

/-- `br`, `cond_br` and `ret` end a block. -/
def Op.isTerminator : Op → Bool
  | .br | .condBr | .ret _ => true
  | _ => false

/-- `br` has one successor and `cond_br` two; no other op has any. -/
def Op.succCount : Op → Nat
  | .br => 1
  | .condBr => 2
  | _ => 0

end Core

instance : DialectSignature CoreDialect where
  sig := Core.Op.sig
  returnTypes := Core.Op.returnTypes
  isTerminator := Core.Op.isTerminator
  succCount := Core.Op.succCount

end Fir
