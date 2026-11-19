import Fir.Core.LoadText

/-!
How `memSet` is written (ADR-2026-11-18-2131). A fill is written `memset`,
as in C and LLVM. Its one attribute is its ordering, a word, as a copy's
is, and it has no `align(A)`: each access is aligned to one unit. Its
operands are the destination, the value and the length, in C's order, and
it has no result:

* `memset nonatomic %d, %v, %n @1` writes `%n` copies of the unit `%v`
  through `%d`, where `%d` is a pointer, `%v` an integer as wide as a unit
  of `%d`'s memory, and `%n` an integer of any width.

The memory, the value's width and the length's width are the operands'
types, so the op writes none of its own. Every ordering decodes, and M1's
validation accepts only `nonatomic`, as for `load`. Whether the value is
as wide as a unit is the rule of the module's data layout, so a value of
any width decodes. A pointer operand, two integer operands and no result
decode; an alignment and any other shape do not.
-/

namespace Fir.Core

open Memory

/-- Reads a fill: its ordering alone, a pointer operand, two integer
operands and no result. -/
def decodeMemSet : List Attr → List Ty → List Ty → Option Op
  | [.word ow], [.ptr n, .int v, .int w], [] => (decodeOrdering ow).map fun o => .memSet o v w n
  | _, _, _ => none

-- The spelling of the example above.
#guard decodeMemSet [.word "nonatomic"] [.ptr 0, .int 8, .int 64] [] ==
  some (.memSet .nonatomic 8 64 0)
-- An atomic ordering decodes; validation rejects it. So does a value of
-- any width; the data layout rejects one that is not a unit's.
#guard decodeMemSet [.word "seq_cst"] [.ptr 3, .int 16, .int 1] [] ==
  some (.memSet .seqCst 16 1 3)
#guard decodeMemSet [.word "nonatomic"] [.ptr 0, .int 32, .int 8] [] ==
  some (.memSet .nonatomic 32 8 0)
-- No ordering, an alignment, a pointer in the value's place, a float
-- value, a missing length, or a result do not decode.
#guard (decodeMemSet [] [.ptr 0, .int 8, .int 64] []).isNone
#guard (decodeMemSet [.word "nonatomic", .app "align" [.int 4]] [.ptr 0, .int 8, .int 64]
  []).isNone
#guard (decodeMemSet [.word "nonatomic"] [.ptr 0, .ptr 0, .int 64] []).isNone
#guard (decodeMemSet [.word "nonatomic"] [.ptr 0, .float 2 5, .int 64] []).isNone
#guard (decodeMemSet [.word "nonatomic"] [.ptr 0, .int 8] []).isNone
#guard (decodeMemSet [.word "nonatomic"] [.ptr 0, .int 8, .int 64] [.int 64]).isNone

end Fir.Core
