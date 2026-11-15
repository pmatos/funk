import Fir.Gpu.Ops
import Fir.Core.TypeText

/-!
The text of `gpu` (ADR-2026-11-09-1545). An op is written as its name, then
its dimension: `%i: i32 = gpu.work_item_id gpu.x`. Every word of the
dialect is written under its name, `gpu`, so in the sum of the core and
`gpu` each word goes to its own side (ADR-2026-11-09-1543).

An op decodes from its name, one dimension word, no operand and one integer
result of any width. Every other shape does not decode: a dimension other
than `gpu.x`, `gpu.y` and `gpu.z`, no dimension or two, an operand, or a
result that is not one integer. The width is the validation rule's: an
`i64` result decodes, and validation rejects it.

The dialect writes and reads its types as the core does, since they are
the core's.
-/

namespace Fir.Gpu

/-- The word of each dimension. -/
def Dim.word : Dim → String
  | .x => "gpu.x"
  | .y => "gpu.y"
  | .z => "gpu.z"

/-- The dimension a word names. -/
def Dim.decode : String → Option Dim
  | "gpu.x" => some .x
  | "gpu.y" => some .y
  | "gpu.z" => some .z
  | _ => none

/-- The name of the op that asks each question. -/
def Query.name : Query → String
  | .workItemId => "gpu.work_item_id"
  | .workGroupId => "gpu.work_group_id"
  | .workGroupSize => "gpu.work_group_size"
  | .numWorkGroups => "gpu.num_work_groups"

/-- The question that an op's name asks. -/
def Query.decode : String → Option Query
  | "gpu.work_item_id" => some .workItemId
  | "gpu.work_group_id" => some .workGroupId
  | "gpu.work_group_size" => some .workGroupSize
  | "gpu.num_work_groups" => some .numWorkGroups
  | _ => none

/-- The name of an op of `gpu`. -/
def Op.name : Op → String
  | .query q _ _ => q.name

/-- The attributes of an op of `gpu`: its dimension. -/
def Op.attrs : Op → List Attr
  | .query _ d _ => [.word d.word]

/-- The op of `gpu` with this name and these attributes, at these operand
and result types. -/
def Op.decode (n : String) (as : List Attr) (ts rs : List (Core.Ty ⊕ Empty)) : Option Op :=
  match Query.decode n, as, ts, rs with
  | some q, [.word w], [], [.inl (.int r)] => (Dim.decode w).map fun d => .query q d r
  | _, _, _, _ => none

/-- `gpu` writes the core's types as the core does. -/
def tyAttr : Core.Ty ⊕ Empty → Attr
  | .inl t => t.attr
  | .inr e => e.elim

/-- `gpu` reads the core's types as the core does. -/
def decodeTy (a : Attr) : Option (Core.Ty ⊕ Empty) := (Core.Ty.decode a).map .inl

instance instDialectText : DialectText GpuDialect where
  opName := Op.name
  opAttrs := Op.attrs
  decodeOp := Op.decode
  tyAttr := tyAttr
  decodeTy := decodeTy

#guard Op.decode "gpu.work_item_id" [.word "gpu.x"] [] [.inl (.int 32)] ==
  some (.query .workItemId .x 32)
#guard Op.decode "gpu.num_work_groups" [.word "gpu.z"] [] [.inl (.int 64)] ==
  some (.query .numWorkGroups .z 64)
#guard (Op.decode "gpu.work_item_id" [.word "gpu.w"] [] [.inl (.int 32)]).isNone
#guard (Op.decode "gpu.work_item_id" [.word "x"] [] [.inl (.int 32)]).isNone
#guard (Op.decode "gpu.work_item_id" [] [] [.inl (.int 32)]).isNone
#guard (Op.decode "gpu.work_item_id" [.word "gpu.x"] [.inl (.int 32)] [.inl (.int 32)]).isNone
#guard (Op.decode "gpu.work_item_id" [.word "gpu.x"] [] [.inl (.ptr 0)]).isNone
#guard (Op.decode "gpu.barrier" [.word "gpu.x"] [] [.inl (.int 32)]).isNone

end Fir.Gpu
