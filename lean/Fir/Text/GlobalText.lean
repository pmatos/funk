import Fir.Text.Grammar

/-!
# Globals in text

A global is an item of the core's kind `global`, written with the one
production of an item, with no parameters, no results and an empty body
(ADR-2026-11-09-1546; ADR-2026-11-19-0124 gives the spelling). Its
attributes come in this order:

* `memory(N)` for a global of the memory `N`, written only when `N` is not
  0: a global of the default memory writes none, so `memory(0)` does not
  decode;
* `size(S)` and `align(A)`;
* the word `const` for a constant global, then the word `export` for an
  exported one;
* the pieces of its initializer, in order: `units(U, …)` for units given
  one by one, `zeros(N)` for `N` zero units, and `addr(@s)` or `addr(@s, K)`
  for the address of the global `@s` plus `K` units, `K` not 0.

For example `global @msg() size(8) align(1) const units(104, 105, 0) {`,
then `}` on the next line. Every number but a unit's is at most
`2^64 - 1`. A unit is any natural number: validation bounds it by its
memory's unit width. Every other attribute, and these in another order, do
not decode, so each global has one spelling. The words `global` and
`const` are ADR-2026-11-09-1546's, as the human ruled on 2026-11-20 (#237
Q4). The core's text writes them too, as `alloca`'s kind hook and as an
op, so the G0 check lists them among the words generic code shares with
the core.
-/

namespace Fir

/-- How a piece of an initializer is written. -/
def InitPiece.attr : InitPiece → Attr
  | .units us => .app "units" (us.map fun (u : Nat) => Attr.int u)
  | .zeros n => .app "zeros" [.int n]
  | .addr s k => .app "addr" (.sym s :: if k = 0 then [] else [.int k])

/-- How a global writes its attributes: its memory when it is not 0, its
size and alignment, `const` and `export` when they hold, then the pieces
of its initializer. -/
def Global.attrs (g : Global) : List Attr :=
  (if g.mem = 0 then [] else [.app "memory" [.int g.mem]]) ++
    .app "size" [.int g.size] :: .app "align" [.int g.align] ::
    ((if g.const then [.word "const"] else []) ++
      ((if g.linkage = .exported then [.word "export"] else []) ++ g.init.map InitPiece.attr))

/-- A global as the one production of an item writes it: the kind
`global`, its symbol, no parameters or results, and its attributes. -/
def Global.item {d : Dialect} (g : Global) : DialectItem d := ⟨"global", g.name, [], [], g.attrs⟩

/-- The unit that an integer of `units(…)` writes: any natural number. -/
def InitPiece.decodeUnit : Attr → Option Nat
  | .int i => if 0 ≤ i then some i.toNat else none
  | _ => none

/-- The piece of an initializer that an attribute writes, if any. -/
def InitPiece.decode : Attr → Option InitPiece
  | .app h xs =>
    if h = "units" then (xs.mapM InitPiece.decodeUnit).map .units
    else if h = "zeros" then
      match xs with
      | [.int n] => (Aggregate.number n).map .zeros
      | _ => none
    else if h = "addr" then
      match xs with
      | [.sym s] => some (.addr s 0)
      | [.sym s, .int k] =>
        (Aggregate.number k).bind fun k => if k = 0 then none else some (.addr s k)
      | _ => none
    else none
  | _ => none

/-- Where a global's attributes stop decoding, and why: the index of the
attribute that does not decode, or none when the global has too few, which
is reported at its kind. -/
abbrev GlobalFault := Option Nat × String

/-- Why a global's `memory(…)` does not decode. -/
def Global.noMemory : String :=
  "a global writes memory(N) first, N from 1 to 2^64 - 1, and no memory for memory 0"

/-- Reads a global's memory: `memory(N)` first, `N` from 1 to the limit,
and memory 0 when the first attribute is not `memory(…)`. Gives the memory,
the index of the next attribute and the attributes after it. -/
def Global.decodeMem : List Attr → Except GlobalFault (Nat × Nat × List Attr)
  | a@(.app h _) :: rest =>
    if h = "memory" then
      match Aggregate.decodeNumber "memory" a with
      | some n => if n = 0 then .error (some 0, Global.noMemory) else .ok (n, 1, rest)
      | none => .error (some 0, Global.noMemory)
    else .ok (0, 0, a :: rest)
  | as => .ok (0, 0, as)

/-- Reads the word `w` when it comes first: whether it does, and the
attributes after it. -/
def Global.decodeFlag (w : String) : List Attr → Bool × List Attr
  | .word w' :: rest => if w' = w then (true, rest) else (false, .word w' :: rest)
  | as => (false, as)

/-- Reads the pieces of an initializer, the first at the index `i`: each
attribute is a piece, or the first that is not one is the fault. -/
def Global.decodePieces (i : Nat) (as : List Attr) : Except GlobalFault (List InitPiece) :=
  match as.mapM InitPiece.decode with
  | some ps => .ok ps
  | none => .error (some (i + as.findIdx fun a => (InitPiece.decode a).isNone),
      "not a piece of a global's initializer, which is written " ++
        "units(U, ...), zeros(N), addr(@s) or addr(@s, K), each number but a unit at most " ++
        "2^64 - 1 and K not 0")

/-- Reads the global `name` from its attributes (ADR-2026-11-19-0124): its
memory, its size and alignment, `const`, `export`, then its pieces. -/
def Global.decodeAttrs (name : Name) (as : List Attr) : Except GlobalFault Global := do
  let (mem, i, as) ← Global.decodeMem as
  match as with
  | s :: a :: rest =>
    match Aggregate.decodeNumber "size" s, Aggregate.decodeNumber "align" a with
    | some size, some align =>
      let (c, rest) := Global.decodeFlag "const" rest
      let (e, rest) := Global.decodeFlag "export" rest
      let init ← Global.decodePieces (i + 2 + c.toNat + e.toNat) rest
      pure ⟨name, mem, size, align, c, if e then .exported else .internal, init⟩
    | none, _ => .error (some i, "a global writes size(S) after its memory, S at most 2^64 - 1")
    | _, none => .error (some (i + 1), "a global writes align(A) after its size, " ++
        "A at most 2^64 - 1")
  | _ => .error (none, "a global writes size(S) and align(A), then const, export and its " ++
      "initializer")

end Fir
