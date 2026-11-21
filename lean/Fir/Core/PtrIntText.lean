import Fir.Core.Signature

/-!
How `ptrExpose` and `ptrFromInt` are written (#232; the human's ruling of
2026-11-18, Q1). They are written `ptr_expose` and `ptr_from_int`, bare
words as every core op's name is (ADR-2026-11-09-1543), and have no
attributes:

* `%a: i64 = ptr_expose %p @1` exposes the pointer `%p` and gives its
  address;
* `%q: ptr = ptr_from_int %a @1` turns the integer `%a` back into a
  pointer.

The memory and the integer's width are the types of the operand and the
result, so the ops write none of their own. Whether the integer is as wide
as the memory's pointers, and whether the memory is integral, is the rule
of the module's data layout, so an integer of any width decodes. One
operand and one result of the shapes above decode; an attribute and any
other shape do not.
-/

namespace Fir.Core

/-- Reads `ptr_expose`: a pointer, giving an integer, without attributes. -/
def decodePtrExpose (as : List Attr) : List Ty → List Ty → Option Op
  | [.ptr n], [.int w] => if as.isEmpty then some (.ptrExpose n w) else none
  | _, _ => none

/-- Reads `ptr_from_int`: an integer, giving a pointer, without
attributes. -/
def decodePtrFromInt (as : List Attr) : List Ty → List Ty → Option Op
  | [.int w], [.ptr n] => if as.isEmpty then some (.ptrFromInt n w) else none
  | _, _ => none

/-- `ptr_expose` decodes only from no attributes, a pointer operand and an
integer result. -/
theorem decodePtrExpose_eq {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodePtrExpose as ts rs = some op) :
    ∃ n w, as = [] ∧ ts = [.ptr n] ∧ rs = [.int w] ∧ op = .ptrExpose n w := by
  unfold decodePtrExpose at h
  split at h
  · split at h
    · cases h
      exact ⟨_, _, List.isEmpty_iff.mp ‹_›, rfl, rfl, rfl⟩
    · cases h
  · cases h

/-- `ptr_from_int` decodes only from no attributes, an integer operand and
a pointer result. -/
theorem decodePtrFromInt_eq {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodePtrFromInt as ts rs = some op) :
    ∃ n w, as = [] ∧ ts = [.int w] ∧ rs = [.ptr n] ∧ op = .ptrFromInt n w := by
  unfold decodePtrFromInt at h
  split at h
  · split at h
    · cases h
      exact ⟨_, _, List.isEmpty_iff.mp ‹_›, rfl, rfl, rfl⟩
    · cases h
  · cases h

-- The spellings of the examples above, at any width.
#guard decodePtrExpose [] [.ptr 0] [.int 64] == some (.ptrExpose 0 64)
#guard decodePtrFromInt [] [.int 32] [.ptr 1] == some (.ptrFromInt 1 32)
-- An attribute, a pointer result of `ptr_expose`, an integer result of
-- `ptr_from_int`, or a second operand do not decode.
#guard (decodePtrExpose [.word "nonatomic"] [.ptr 0] [.int 64]).isNone
#guard (decodePtrExpose [] [.ptr 0] [.ptr 0]).isNone
#guard (decodePtrFromInt [] [.int 64] [.int 64]).isNone
#guard (decodePtrFromInt [] [.int 64, .int 64] [.ptr 0]).isNone

end Fir.Core
