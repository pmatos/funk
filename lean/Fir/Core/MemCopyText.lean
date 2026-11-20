import Fir.Core.LoadText

/-!
How `memCopy` is written (ADR-2026-11-18-2131). A copy is written
`memcpy` and a move `memmove`, as in C and LLVM. Its one attribute is its
ordering, a word, as a load's is, and it has no `align(A)`: each access is
aligned to one unit. Its operands are the destination, the source and the
length, in C's order, and it has no result:

* `memcpy nonatomic %d, %s, %n @1` copies `%n` units from `%s` to `%d`,
  where `%d` and `%s` are pointers of one memory and `%n` an integer of any
  width;
* `memmove nonatomic %d, %s, %n @1` moves them.

The memory and the length's width are the operands' types, so the op
writes none of its own. Every ordering decodes, and M1's validation accepts
only `nonatomic`, as for `load`. Two pointer operands of one memory, an
integer operand and no result decode; an alignment, pointers of two
memories and any other shape do not.
-/

namespace Fir.Core

open Memory

/-- The name of a copy, `memcpy`, and of a move, `memmove`. -/
def CopyKind.name : CopyKind → String
  | .copy => "memcpy"
  | .move => "memmove"

/-- Reads a copy or a move of the kind `k`: its ordering alone, two pointer
operands of one memory, an integer operand and no result. -/
def decodeMemCopy (k : CopyKind) : List Attr → List Ty → List Ty → Option Op
  | [.word ow], [.ptr n, .ptr n', .int w], [] =>
    if n = n' then (decodeOrdering ow).map fun o => .memCopy k o w n else none
  | _, _, _ => none

-- The spellings of the examples above.
#guard decodeMemCopy .copy [.word "nonatomic"] [.ptr 0, .ptr 0, .int 64] [] ==
  some (.memCopy .copy .nonatomic 64 0)
#guard decodeMemCopy .move [.word "nonatomic"] [.ptr 3, .ptr 3, .int 8] [] ==
  some (.memCopy .move .nonatomic 8 3)
-- An atomic ordering decodes; validation rejects it.
#guard decodeMemCopy .copy [.word "seq_cst"] [.ptr 0, .ptr 0, .int 1] [] ==
  some (.memCopy .copy .seqCst 1 0)
-- No ordering, an alignment, pointers of two memories, an integer in a
-- pointer's place, a missing length, or a result do not decode.
#guard (decodeMemCopy .copy [] [.ptr 0, .ptr 0, .int 64] []).isNone
#guard (decodeMemCopy .copy [.word "nonatomic", .app "align" [.int 4]] [.ptr 0, .ptr 0, .int 64]
  []).isNone
#guard (decodeMemCopy .move [.word "nonatomic"] [.ptr 0, .ptr 1, .int 64] []).isNone
#guard (decodeMemCopy .move [.word "nonatomic"] [.int 64, .ptr 0, .int 64] []).isNone
#guard (decodeMemCopy .copy [.word "nonatomic"] [.ptr 0, .ptr 0] []).isNone
#guard (decodeMemCopy .copy [.word "nonatomic"] [.ptr 0, .ptr 0, .int 64] [.int 64]).isNone

end Fir.Core
