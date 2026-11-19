import Fir.Core.Signature

/-!
How `fieldAddr` is written (#236). Its attributes are the symbol of the
aggregate's layout that it reads and the number of the field, counted from
0, as a call writes its callee's symbol; its operands are the pointer, and
the index of an element after it when it takes one. Its memory is the
memory of its pointer and its result:

* `%q: ptr = fieldaddr @pair 1 %p @1` gives the address of the field 1 of
  `@pair`, from a pointer `%p` to the layout in memory 0;
* `%e: ptr(1) = fieldaddr @row 0 %p, %k @1` gives the address of the
  element `%k` of the field 0 of `@row`, from a pointer of memory 1.

The field's number decodes when it is not negative, and the index at any
width. A pointer result of another memory, an integer result, or other
operands do not decode, and neither does any other list of attributes.
Validation says which layouts and fields an op may name.
-/

namespace Fir.Core

/-- The attributes of `fieldAddr s i`: the symbol of its layout and the
number of its field. -/
def fieldAddrAttrs (s : String) (i : Nat) : List Attr := [.sym s, .int i]

/-- Reads `fieldAddr`: the symbol of a layout and a field's number that is
not negative, a pointer, then an integer when it takes an index, and a
pointer of the same memory. -/
def decodeFieldAddr (as : List Attr) : List Ty → List Ty → Option Op
  | [.ptr n], [.ptr n'] => match as with
    | [.sym s, .int i] => if 0 ≤ i ∧ n = n' then some (.fieldAddr s i.toNat n none) else none
    | _ => none
  | [.ptr n, .int w], [.ptr n'] => match as with
    | [.sym s, .int i] => if 0 ≤ i ∧ n = n' then some (.fieldAddr s i.toNat n (some w)) else none
    | _ => none
  | _, _ => none

#guard decodeFieldAddr [.sym "pair", .int 1] [.ptr 0] [.ptr 0] ==
  some (.fieldAddr "pair" 1 0 none)
#guard decodeFieldAddr [.sym "row", .int 0] [.ptr 1, .int 64] [.ptr 1] ==
  some (.fieldAddr "row" 0 1 (some 64))
-- A negative field, a result of another memory, a missing symbol, an
-- integer pointer and a float index do not decode.
#guard (decodeFieldAddr [.sym "pair", .int (-1)] [.ptr 0] [.ptr 0]).isNone
#guard (decodeFieldAddr [.sym "pair", .int 1] [.ptr 0] [.ptr 1]).isNone
#guard (decodeFieldAddr [.int 1] [.ptr 0] [.ptr 0]).isNone
#guard (decodeFieldAddr [.sym "pair", .int 1] [.int 64] [.ptr 0]).isNone
#guard (decodeFieldAddr [.sym "pair", .int 1] [.ptr 0, .float 8 23] [.ptr 0]).isNone

/-- Each `fieldAddr` reads back from how it is written. -/
theorem decodeFieldAddr_attrs (s : String) (j n : Nat) (w : Option Nat) :
    decodeFieldAddr (fieldAddrAttrs s j) (Op.sig (.fieldAddr s j n w)) [.ptr n] =
      some (.fieldAddr s j n w) := by
  cases w <;> simp [decodeFieldAddr, fieldAddrAttrs, Op.sig, i]

/-- `fieldAddr` decodes only from its own attributes, a pointer and an index
when it takes one, and a pointer of the same memory. -/
theorem decodeFieldAddr_eq {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeFieldAddr as ts rs = some op) :
    ∃ s i n w, op = .fieldAddr s i n w ∧ fieldAddrAttrs s i = as ∧ op.sig = ts ∧
      op.returnTypes = rs := by
  unfold decodeFieldAddr at h
  split at h
  · split at h
    · split at h
      · rename_i hc
        obtain ⟨hi, rfl⟩ := hc
        cases h
        exact ⟨_, _, _, _, rfl, by simp [fieldAddrAttrs, Int.toNat_of_nonneg hi], rfl, rfl⟩
      · cases h
    · cases h
  · split at h
    · split at h
      · rename_i hc
        obtain ⟨hi, rfl⟩ := hc
        cases h
        exact ⟨_, _, _, _, rfl, by simp [fieldAddrAttrs, Int.toNat_of_nonneg hi], rfl, rfl⟩
      · cases h
    · cases h
  · cases h

end Fir.Core
