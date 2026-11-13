import Fir.Core.Ops
import Fir.Syntax.Module

/-!
The core dialect is fir's first dialect. Its signature gives the operand and
result types of every core op, and says which ops end a block and how many
successors they have.

This section gives, in order: the core dialect, the types of each op's
operands and results, the terminators and their successors with the
signature that these make up, and a shorthand that the examples use to
write an op.
-/

namespace Fir

/-- The core dialect: the M0 op instances and the M0 types. -/
abbrev CoreDialect : Dialect := ⟨Core.Op, Core.Ty⟩

namespace Core

/-- `iN` with `N = w`. -/
abbrev i (w : Nat) : Ty := .int w

/-- The operand types of each core op. -/
def Op.sig : Op → List Ty
  | .const _ _ | .fconst .. | .poison _ | .br | .unreachable => []
  | .add w _ | .sub w _ | .mul w _ | .sdiv w _ | .udiv w _ | .srem w | .urem w
  | .and w | .or w | .xor w | .shl w | .lshr w | .ashr w | .icmp _ w => [i w, i w]
  | .fcmp _ e m | .fbin _ e m => [.float e m, .float e m]
  | .funary _ e m => [.float e m]
  | .fma e m => [.float e m, .float e m, .float e m]
  | .select w => [i 1, i w, i w]
  | .zext m _ | .sext m _ | .trunc m _ => [i m]
  | .toBits e m => [.float e m]
  | .ofBits e m => [i (floatWidth e m)]
  | .sitofp n .. | .uitofp n .. => [i n]
  | .fpext e m .. | .fptrunc e m .. | .fptosi e m _ | .fptoui e m _ => [.float e m]
  | .freeze w => [i w]
  | .condBr => [i 1]
  | .ret ts => ts
  | .call _ ts _ => ts

/-- The result types of each core op. -/
def Op.returnTypes : Op → List Ty
  | .const w _ | .add w _ | .sub w _ | .mul w _ | .sdiv w _ | .udiv w _
  | .srem w | .urem w | .and w | .or w | .xor w | .shl w | .lshr w | .ashr w
  | .select w | .freeze w | .poison w => [i w]
  | .fconst e m _ | .fbin _ e m | .funary _ e m | .fma e m => [.float e m]
  | .icmp _ _ | .fcmp .. => [i 1]
  | .zext _ n | .sext _ n | .trunc _ n => [i n]
  | .toBits e m => [i (floatWidth e m)]
  | .ofBits e m => [.float e m]
  | .sitofp _ e m | .uitofp _ e m => [.float e m]
  | .fpext _ _ e' m' | .fptrunc _ _ e' m' => [.float e' m']
  | .fptosi _ _ n | .fptoui _ _ n => [i n]
  | .br | .condBr | .ret _ | .unreachable => []
  | .call _ _ rs => rs

/-- `br`, `cond_br`, `ret` and `unreachable` end a block. -/
def Op.isTerminator : Op → Bool
  | .br | .condBr | .ret _ | .unreachable => true
  | _ => false

/-- `br` has one successor and `cond_br` two; no other op has any. -/
def Op.succCount : Op → Nat
  | .br => 1
  | .condBr => 2
  | _ => 0

/-- A core op with no regions: its results, op instance, operands, location
reference and successors. The examples and checks of this spec build their
ops with it. -/
def op (results : List (Name × Ty)) (o : Op) (operands : List Name) (loc : LocRef := 0)
    (succs : List Succ := []) : Operation CoreDialect :=
  { results, op := o, operands, succs, regions := [], loc }

end Core

instance : DialectSignature CoreDialect where
  sig := Core.Op.sig
  returnTypes := Core.Op.returnTypes
  isTerminator := Core.Op.isTerminator
  succCount := Core.Op.succCount

end Fir
