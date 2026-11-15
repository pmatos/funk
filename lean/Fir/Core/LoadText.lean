import Fir.Core.AllocaText
import Fir.Memory.Ordering

/-!
How `load` is written. Its attributes are its ordering, a word, and
`align(A)` when it gives an alignment, separated by spaces as every op's
attributes are; its one operand is the pointer it loads through, and its
result type is the integer or pointer type it loads:

* `%v: i32 = load nonatomic %p @1` loads an `i32` through `%p`, at the
  natural alignment of `i32` in the memory of `%p`;
* `%v: i8 = load nonatomic align(4) %q @1` loads an `i8` through `%q`, an
  access aligned to 4 units;
* `%r: ptr(1) = load nonatomic %p @1` loads a pointer of memory 1 through
  `%p`: that is `loadPtr`.

Each ordering is a word: `nonatomic`, and the atomic orderings
`unordered`, `monotonic`, `acquire`, `release`, `acq_rel` and `seq_cst`.
Each decodes; M1's validation accepts only `nonatomic`, so the others are
hooks in the format (ADR-2026-11-09-1542). An alignment decodes when it is
not negative, and validation says which are allowed. The ordering is always
written, so each instance has one spelling. An op with one pointer
operand, of any memory, and one integer or pointer result decodes; any
other shape does not. A store writes the same attributes, so the two
read them with one reader.
-/

namespace Fir.Core

open Memory

/-- The word of an ordering. -/
def _root_.Fir.Memory.Ordering.word : Memory.Ordering → String
  | .nonatomic => "nonatomic"
  | .unordered => "unordered"
  | .monotonic => "monotonic"
  | .acquire => "acquire"
  | .release => "release"
  | .acqRel => "acq_rel"
  | .seqCst => "seq_cst"

/-- The ordering that a word names. -/
def decodeOrdering : String → Option Memory.Ordering
  | "nonatomic" => some .nonatomic
  | "unordered" => some .unordered
  | "monotonic" => some .monotonic
  | "acquire" => some .acquire
  | "release" => some .release
  | "acq_rel" => some .acqRel
  | "seq_cst" => some .seqCst
  | _ => none

/-- Each ordering reads back from its word. -/
theorem decodeOrdering_word (o : Memory.Ordering) : decodeOrdering o.word = some o := by
  cases o <;> rfl

/-- The attributes of `load o w a n`: its ordering, and its alignment when it
gives one. -/
def loadAttrs (o : Memory.Ordering) (a : Option Nat) : List Attr :=
  .word o.word :: a.toList.map fun (a : Nat) => .app "align" [.int a]

/-- Reads the attributes of a load or a store: its ordering and an
alignment. -/
def decodeAccess : List Attr → Option (Memory.Ordering × Option Nat)
  | .word ow :: rest => do
    let o ← decodeOrdering ow
    (decodeAlign rest).map (o, ·)
  | _ => none

/-- Reads `load`: one pointer operand, one integer or pointer result, its
ordering and an alignment. -/
def decodeLoad (as : List Attr) : List Ty → List Ty → Option Op
  | [.ptr n], [.int w] => (decodeAccess as).map fun (o, a) => .load o w a n
  | [.ptr n], [.ptr mp] => (decodeAccess as).map fun (o, a) => .loadPtr o mp a n
  | _, _ => none

-- The spellings of the examples above.
#guard decodeLoad [.word "nonatomic"] [.ptr 0] [.int 32] == some (.load .nonatomic 32 none 0)
#guard decodeLoad [.word "nonatomic", .app "align" [.int 4]] [.ptr 1] [.int 8] ==
  some (.load .nonatomic 8 (some 4) 1)
-- A pointer result loads a pointer of its memory.
#guard decodeLoad [.word "nonatomic"] [.ptr 0] [.ptr 2] == some (.loadPtr .nonatomic 2 none 0)
-- An atomic ordering and an alignment that is not a power of two decode;
-- validation rejects them.
#guard decodeLoad [.word "seq_cst"] [.ptr 0] [.int 64] == some (.load .seqCst 64 none 0)
#guard (decodeLoad [.word "nonatomic", .app "align" [.int 3]] [.ptr 0] [.int 32]).isSome
-- No ordering, a misspelled one, a negative alignment, a second pointer, a
-- float result, or an integer operand do not decode.
#guard (decodeLoad [] [.ptr 0] [.int 32]).isNone
#guard (decodeLoad [.word "relaxed"] [.ptr 0] [.int 32]).isNone
#guard (decodeLoad [.word "nonatomic", .app "align" [.int (-4)]] [.ptr 0] [.int 32]).isNone
#guard (decodeLoad [.word "nonatomic"] [.ptr 0, .ptr 0] [.int 32]).isNone
#guard (decodeLoad [.word "nonatomic"] [.ptr 0] [.float 8 23]).isNone
#guard (decodeLoad [.word "nonatomic"] [.int 64] [.int 32]).isNone

end Fir.Core
