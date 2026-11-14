import Fir.Core.Ops
import Fir.Core.TypeText

/-!
How `alloca` is written (ADR-2026-11-14-0915). Its attributes are its kind,
the type it allocates, its count when it is not 1, and `align(A)` when it
gives an alignment, separated by spaces as every op's attributes are. Its
memory is the memory of its result:

* `%p: ptr = alloca stack i32 @1` allocates room for one `i32` in memory 0,
  at the natural alignment of `i32`;
* `%p: ptr = alloca stack i32 4 @1` allocates room for four;
* `%p: ptr(1) = alloca stack i8 12 align(4) @1` allocates twelve `i8` of
  memory 1, aligned to 4 units.

Each kind of the memory model is a word, `stack`, `global` or `heap`, and
decodes; M1's validation accepts only `stack`, so the kind is a hook in the
format (ADR-2026-11-09-1542). The type is written as a type is, and decodes
with no bound on its width or memory; a count and an alignment decode when
they are not negative. Validation says which of them are allowed. A count
of 1 is not written, so `alloca stack i32 1` does not decode: each
instance has one spelling. An op with no operands and a pointer result
decodes; any other shape does not.
-/

namespace Fir.Core

open Memory

/-- The word of an allocation's kind. -/
def _root_.Fir.Memory.AllocKind.word : AllocKind → String
  | .stack => "stack"
  | .global => "global"
  | .heap => "heap"

/-- The kind that a word names. -/
def decodeKind : String → Option AllocKind
  | "stack" => some .stack
  | "global" => some .global
  | "heap" => some .heap
  | _ => none

/-- Each kind reads back from its word. -/
theorem decodeKind_word (k : AllocKind) : decodeKind k.word = some k := by
  cases k <;> rfl

/-- Reads a core type as `Ty.decode` does, with no bound on a width or a
memory: `alloca` carries its type as an attribute, and validation, not the
text, bounds it, so every type reads back from how it is written. -/
def Ty.decodeAny : Attr → Option Ty
  | .word "ptr" => some (.ptr 0)
  | .word s => match s.toList with
    | 'i' :: ds =>
      let digits := String.ofList ds
      (digits.toNat?).bind fun w => if toString w = digits then some (.int w) else none
    | _ => (aliasFormat s).map fun (e, m) => .float e m
  | .app "float" [.int e, .int m] =>
    if 0 ≤ e ∧ 0 ≤ m ∧ floatAlias e.toNat m.toNat = none then some (.float e.toNat m.toNat)
    else none
  | .app "ptr" [.int n] => if 1 ≤ n then some (.ptr n.toNat) else none
  | _ => none

/-- The attributes of `alloca k t c a`: its kind, its type, its count when
it is not 1, and its alignment when it gives one. -/
def allocaAttrs (k : AllocKind) (t : Ty) (c : Nat) (a : Option Nat) : List Attr :=
  [.word k.word, t.attr] ++ (if c = 1 then [] else [.int c]) ++
    a.toList.map fun a => .app "align" [.int a]

/-- Reads `alloca`'s alignment, after its count: none, or `align(A)` with
`A` not negative. -/
def decodeAlign : List Attr → Option (Option Nat)
  | [] => some none
  | [.app "align" [.int a]] => if 0 ≤ a then some (some a.toNat) else none
  | _ => none

/-- Reads `alloca`: no operands, a pointer result, its kind, its type, a
count that is not negative and not 1, or none for 1, and an alignment. -/
def decodeAlloca (as : List Attr) : List Ty → List Ty → Option Op
  | [], [.ptr n] => match as with
    | .word kw :: ta :: rest => do
      let k ← decodeKind kw
      let t ← Ty.decodeAny ta
      match rest with
      | .int c :: rest' =>
        if 0 ≤ c ∧ c ≠ 1 then (decodeAlign rest').map (.alloca k t c.toNat · n) else none
      | rest' => (decodeAlign rest').map (.alloca k t 1 · n)
    | _ => none
  | _, _ => none

-- The ruling's examples, written with spaces.
#guard decodeAlloca [.word "stack", .word "i32", .int 4] [] [.ptr 0] ==
  some (.alloca .stack (.int 32) 4 none 0)
#guard decodeAlloca [.word "stack", .word "i8", .int 12, .app "align" [.int 4]] [] [.ptr 1] ==
  some (.alloca .stack (.int 8) 12 (some 4) 1)
#guard decodeAlloca [.word "heap", .word "i32"] [] [.ptr 0] ==
  some (.alloca .heap (.int 32) 1 none 0)
-- A negative count, a misspelled kind, an operand or an integer result do
-- not decode.
#guard (decodeAlloca [.word "stack", .word "i32", .int (-1)] [] [.ptr 0]).isNone
#guard (decodeAlloca [.word "stack", .word "i32", .int 1] [] [.ptr 0]).isNone
-- A count of 0, a width past the limit and a float type decode;
-- validation rejects them.
#guard (decodeAlloca [.word "stack", .word "i32", .int 0] [] [.ptr 0]).isSome
#guard (decodeAlloca [.word "stack", .word "i16777216"] [] [.ptr 0]).isSome
#guard (decodeAlloca [.word "stack", .word "f32"] [] [.ptr 0]).isSome
#guard (decodeAlloca [.word "frame", .word "i32"] [] [.ptr 0]).isNone
#guard (decodeAlloca [.word "stack", .word "i32"] [.int 64] [.ptr 0]).isNone
#guard (decodeAlloca [.word "stack", .word "i32"] [] [.int 64]).isNone

end Fir.Core
