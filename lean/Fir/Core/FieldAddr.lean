import Fir.Core.Pointer
import Fir.Core.Signature
import Fir.Execution.RunItems

/-!
# Field address rules

This section gives `fieldAddr` its rule (#236). An aggregate's layout is an
item of the module (ADR-2026-11-16-1546), and the run gives each op's rule
the layouts of its function's table, each field placed: its offset and the
units from one of its elements to the next, its type's units rounded up to
its alignment (the section on the items a run gives each op).
`fieldAddr s i n w` names the layout `s` and its field `i`, and moves its
pointer, of `ptr<N>`, `N = n`, to that field:

* with no index, by the field's offset, so the result points to the field,
  or to the first element of a repeated field;
* with an index `k` of `iW`, `w = some W`, read as signed, by the field's
  offset plus `k` times the field's step, so the result points to the
  element `k` of the field.

In memory 0, the field 1 of `aggregate @pair() memory(0) size(16) align(8)
field(0, i64) field(8, ptr) {` is at offset 8, so `fieldAddr` moves a
pointer to a `@pair` by 8 units; and the element 2 of `field(0, i24, 4)`
is at offset 8, since each `i24` takes 3 units rounded up to its alignment
of 4 (the human's ruling of 2026-11-16 on #236, Q2 B). Units are those of
the layout's memory, whatever their width.

The move is `ptradd`'s: it keeps the pointer's provenance, and the result
may leave the bounds of the allocation, as an index outside the field's
elements does. Only an access through the result must be in bounds, so
one-past-the-end pointers and flexible array members work (the human's
ruling of 2026-11-16 on #236, Q3 A). `fieldAddr` is never UB, and gives
poison only for a poison operand.

Validation requires that `s` name a layout of the op's table in the
memory `N`, that `i` be one of its fields, and that only a repeated field
take an index (the section on the core rules of an op). The rule itself
holds for every record that a run may give: one that has no layout `s`, or
no field `i`, moves the pointer by 0, so the op is never UB and never makes
poison, for every record, with no hypothesis on it.
-/

namespace Fir.Core

open Memory

/-- The units from the start of a layout to the element `k` of its field
`i`, in the layout `l` that a run gives: the field's offset plus `k` times
its step, and 0 when there is no such layout or field. -/
def fieldOffset (l : Option LayoutPlace) (i : Nat) (k : Int) : Int :=
  match l.bind (·.fields[i]?) with
  | some f => f.offset + f.stride * k
  | none => 0

/-- The rule of `fieldAddr` with no index: the pointer moved to the field
`i` of the layout `l`, and poison for a poison pointer. -/
def fieldAddrValue (l : Option LayoutPlace) (i : Nat) : PoisonOr Pointer → PoisonOr Pointer
  | .value p => .value (movePointer p (fieldOffset l i 0))
  | .poison => .poison

/-- The rule of `fieldAddr` with an index: the pointer moved to the element
of the field `i` of the layout `l` that the integer, read as signed, names,
and poison when either operand is poison. -/
def elemAddrValue (l : Option LayoutPlace) (i : Nat) :
    PoisonOr Pointer → PoisonOr (BitVec w) → PoisonOr Pointer
  | .value p, .value k => .value (movePointer p (fieldOffset l i k.toInt))
  | _, _ => .poison

/-- The result of `fieldAddr s j n w` on its operands, in the layout `l`:
the field's address with no index, and the element's with one. -/
def fieldAddrResult (l : Option LayoutPlace) (j : Nat) {s : String} {n : Nat} :
    (w : Option Nat) → HVector toType (Op.sig (.fieldAddr s j n w)) → HVector toType [Ty.ptr n]
  | none, .cons p .nil => .cons (fieldAddrValue l j p) .nil
  | some _, .cons p (.cons k .nil) => .cons (elemAddrValue l j p k) .nil

-- `@pair`, as a run of memory 0 gives it: its field 1 is 8 units into it.
-- A field that it does not have moves the pointer by 0, and so does a
-- layout that the run does not give.
#guard let pair : Option LayoutPlace := some ⟨0, 16, 8, [⟨0, 8, none⟩, ⟨8, 8, none⟩]⟩
  fieldAddrValue pair 1 (.value ⟨some 0, 0⟩) == .value ⟨some 0, 8⟩ &&
  fieldAddrValue pair 2 (.value ⟨some 0, 5⟩) == .value ⟨some 0, 5⟩ &&
  fieldAddrValue none 1 (.value ⟨some 0, 5⟩) == .value ⟨some 0, 5⟩ &&
  -- A pointer without provenance stays without it, and poison gives poison.
  fieldAddrValue pair 1 (.value ⟨none, 0⟩) == .value ⟨none, 8⟩ &&
  fieldAddrValue pair 1 .poison == .poison
-- An `i32`, then four `i24` at offset 4, each 4 units: the element 2 is
-- 4 + 2 * 4 units in, and an index outside the elements moves the pointer
-- as `ptradd` does.
#guard let row : Option LayoutPlace := some ⟨0, 20, 4, [⟨0, 4, none⟩, ⟨4, 4, some 4⟩]⟩
  elemAddrValue row 1 (.value ⟨some 3, 0⟩) (.value (2 : BitVec 32)) == .value ⟨some 3, 12⟩ &&
  elemAddrValue row 1 (.value ⟨some 3, 0⟩) (.value (4 : BitVec 8)) == .value ⟨some 3, 20⟩ &&
  elemAddrValue row 1 (.value ⟨some 3, 0⟩) (.value (-1 : BitVec 8)) == .value ⟨some 3, 0⟩ &&
  elemAddrValue row 1 (.value ⟨some 0, 0⟩) (.poison : PoisonOr (BitVec 32)) == .poison

end Fir.Core
