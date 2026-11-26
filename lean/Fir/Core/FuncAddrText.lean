import Fir.Core.Signature

/-!
How `funcAddr` is written (#235). Its one attribute is the symbol of the
function whose address it gives, as a call writes its callee's symbol; it
takes no operands, and its memory is the memory of its pointer result:

* `%p: ptr = funcaddr @f @1` gives the address of the function `@f`.

An operand, a result that is not one pointer, or any other list of
attributes does not decode. A pointer result of another memory, such as
`ptr(1)`, decodes; validation rejects it, and says which functions an op
may name.
-/

namespace Fir.Core

/-- The attributes of `funcAddr s`: the symbol of its function. -/
def funcAddrAttrs (s : String) : List Attr := [.sym s]

/-- Reads `funcAddr`: the symbol of a function, no operands, and a pointer
result. -/
def decodeFuncAddr (as : List Attr) : List Ty → List Ty → Option Op
  | [], [.ptr n] => match as with
    | [.sym s] => some (.funcAddr s n)
    | _ => none
  | _, _ => none

#guard decodeFuncAddr [.sym "f"] [] [.ptr 0] == some (.funcAddr "f" 0)
#guard decodeFuncAddr [.sym "f"] [] [.ptr 1] == some (.funcAddr "f" 1)
-- An operand, an integer result, a missing symbol and a second attribute
-- do not decode.
#guard (decodeFuncAddr [.sym "f"] [.ptr 0] [.ptr 0]).isNone
#guard (decodeFuncAddr [.sym "f"] [] [.int 64]).isNone
#guard (decodeFuncAddr [] [] [.ptr 0]).isNone
#guard (decodeFuncAddr [.sym "f", .int 0] [] [.ptr 0]).isNone

/-- Each `funcAddr` reads back from how it is written. -/
theorem decodeFuncAddr_attrs (s : String) (n : Nat) :
    decodeFuncAddr (funcAddrAttrs s) (Op.sig (.funcAddr s n)) [.ptr n] =
      some (.funcAddr s n) := rfl

/-- `funcAddr` decodes only from its own attribute, no operands, and a
pointer result. -/
theorem decodeFuncAddr_eq {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeFuncAddr as ts rs = some op) :
    ∃ s n, op = .funcAddr s n ∧ funcAddrAttrs s = as ∧ op.sig = ts ∧
      op.returnTypes = rs := by
  unfold decodeFuncAddr at h
  split at h
  · split at h
    · cases h
      exact ⟨_, _, rfl, rfl, rfl, rfl⟩
    · cases h
  · cases h

end Fir.Core
