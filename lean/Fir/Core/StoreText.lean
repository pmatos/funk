import Fir.Core.LoadText

/-!
How `store` is written. Its attributes are those of `load`, written the
same way: its ordering, a word, and `align(A)` when it gives an alignment,
separated by spaces (ADR-2026-11-14-2316). Its operands are the value it
stores, then the pointer it stores through, and it has no result:

* `store nonatomic %v, %p @1` stores the `i32` `%v` through `%p`, at the
  natural alignment of `i32` in the memory of `%p`, when `%v` is an `i32`;
* `store nonatomic align(4) %b, %q @1` stores the `i8` `%b` through `%q`,
  an access aligned to 4 units, when `%b` is an `i8`;
* `store nonatomic %r, %p @1` stores the pointer `%r` through `%p`, when
  `%r` is a pointer, of any memory: that is `storePtr`.

The type of the value is its operand's, so the op writes none of its own.
Every ordering decodes, and M1's validation accepts only `nonatomic`, as
for `load`. An op with an integer or pointer operand, then a pointer
operand of any memory, and no result decodes; any other shape does not.
-/

namespace Fir.Core

open Memory

/-- Reads `store`: an integer or pointer operand, then a pointer operand,
no result, its ordering and an alignment. -/
def decodeStore (as : List Attr) : List Ty → List Ty → Option Op
  | [.int w, .ptr n], [] => (decodeAccess as).map fun (o, a) => .store o w a n
  | [.ptr mp, .ptr n], [] => (decodeAccess as).map fun (o, a) => .storePtr o mp a n
  | _, _ => none

-- The spellings of the examples above.
#guard decodeStore [.word "nonatomic"] [.int 32, .ptr 0] [] == some (.store .nonatomic 32 none 0)
#guard decodeStore [.word "nonatomic", .app "align" [.int 4]] [.int 8, .ptr 1] [] ==
  some (.store .nonatomic 8 (some 4) 1)
#guard decodeStore [.word "nonatomic"] [.ptr 2, .ptr 0] [] == some (.storePtr .nonatomic 2 none 0)
-- An atomic ordering and an alignment that is not a power of two decode;
-- validation rejects them.
#guard decodeStore [.word "release"] [.int 64, .ptr 0] [] == some (.store .release 64 none 0)
#guard (decodeStore [.word "nonatomic", .app "align" [.int 3]] [.int 32, .ptr 0] []).isSome
-- No ordering, a misspelled one, a negative alignment, an integer in the
-- pointer's place, a float value, one operand, or a result do not decode.
#guard (decodeStore [] [.int 32, .ptr 0] []).isNone
#guard (decodeStore [.word "relaxed"] [.int 32, .ptr 0] []).isNone
#guard (decodeStore [.word "nonatomic", .app "align" [.int (-4)]] [.int 32, .ptr 0] []).isNone
#guard (decodeStore [.word "nonatomic"] [.ptr 0, .int 32] []).isNone
#guard (decodeStore [.word "nonatomic"] [.float 8 23, .ptr 0] []).isNone
#guard (decodeStore [.word "nonatomic"] [.ptr 0] []).isNone
#guard (decodeStore [.word "nonatomic"] [.int 32, .ptr 0] [.int 32]).isNone

end Fir.Core
