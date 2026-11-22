import Fir.Core.Signature

/-!
How `globalAddr` is written (#237). Its one attribute is the symbol of the
global whose address it gives, as a call writes its callee's symbol; it
takes no operands, and its memory is the memory of its pointer result:

* `%p: ptr = globaladdr @msg @1` gives the address of `@msg`, a global of
  memory 0;
* `%q: ptr(1) = globaladdr @cell @1` gives the address of `@cell`, a global
  of memory 1.

An operand, a result that is not one pointer, or any other list of
attributes does not decode. Validation says which globals an op may name.
-/

namespace Fir.Core

/-- The attributes of `globalAddr s`: the symbol of its global. -/
def globalAddrAttrs (s : String) : List Attr := [.sym s]

/-- Reads `globalAddr`: the symbol of a global, no operands, and a pointer
result. -/
def decodeGlobalAddr (as : List Attr) : List Ty → List Ty → Option Op
  | [], [.ptr n] => match as with
    | [.sym s] => some (.globalAddr s n)
    | _ => none
  | _, _ => none

#guard decodeGlobalAddr [.sym "msg"] [] [.ptr 0] == some (.globalAddr "msg" 0)
#guard decodeGlobalAddr [.sym "cell"] [] [.ptr 1] == some (.globalAddr "cell" 1)
-- An operand, an integer result, a missing symbol and a second attribute
-- do not decode.
#guard (decodeGlobalAddr [.sym "msg"] [.ptr 0] [.ptr 0]).isNone
#guard (decodeGlobalAddr [.sym "msg"] [] [.int 64]).isNone
#guard (decodeGlobalAddr [] [] [.ptr 0]).isNone
#guard (decodeGlobalAddr [.sym "msg", .int 0] [] [.ptr 0]).isNone

/-- Each `globalAddr` reads back from how it is written. -/
theorem decodeGlobalAddr_attrs (s : String) (n : Nat) :
    decodeGlobalAddr (globalAddrAttrs s) (Op.sig (.globalAddr s n)) [.ptr n] =
      some (.globalAddr s n) := rfl

/-- `globalAddr` decodes only from its own attribute, no operands, and a
pointer result. -/
theorem decodeGlobalAddr_eq {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeGlobalAddr as ts rs = some op) :
    ∃ s n, op = .globalAddr s n ∧ globalAddrAttrs s = as ∧ op.sig = ts ∧
      op.returnTypes = rs := by
  unfold decodeGlobalAddr at h
  split at h
  · split at h
    · cases h
      exact ⟨_, _, rfl, rfl, rfl, rfl⟩
    · cases h
  · cases h

end Fir.Core
