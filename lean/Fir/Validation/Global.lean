import Fir.Validation.Layout

/-!
A global names a block of units of one memory, with its initial units
(ADR-2026-11-09-1546). It is valid in a module whose data layout is `l`,
as an item of a symbol table whose globals are `gs`, when its numbers are at most
`2^64 - 1`, so that the text can write it, the module has its memory, its
alignment is valid as an entry's is, each piece of its initializer fits,
and the initializer takes no more units than the global's size.

A piece of `units(…)` fits when each of its units is below `2^U`, where
`U` is the unit width of the global's memory. A piece `addr(@s, K)` fits
when `@s` names a global of `gs`, the global's own table's: an item names
only items of its own table, as an op does (ADR-2026-11-10-1510). It takes
the units of one pointer of `@s`'s memory in the global's memory, as a
pointer stored there does (ADR-2026-11-12-2125). A function's address is
an allocation of kind `function` (the human's ruling of 2026-11-19 on
#235), so a function's address in an initializer waits until runs make
those allocations. The units past the initializer are the run's question,
not validation's.
-/

namespace Fir

/-- The global of the symbol `s` among the globals `gs` of a table: the
first with that symbol. -/
def Global.named? (gs : List Global) (s : Name) : Option Global :=
  gs.find? (·.name == s)

/-- The units that a piece of an initializer takes in the memory `n` of a
module whose data layout is `l`, as an item of a table whose globals are
`gs`: one for each unit it gives, its count of zeros, or the units of one
pointer of the memory of the global whose address it gives, and none when
`gs` has no such global. -/
def InitPiece.unitCount (l : DataLayout) (gs : List Global) (n : Nat) : InitPiece → Nat
  | .units us => us.length
  | .zeros k => k
  | .addr s _ =>
    match Global.named? gs s with
    | some h => (l.entry n).bitsUnits (l.entry h.mem).pointer
    | none => 0

/-- The units that a global's initializer takes, as an item of a table
whose globals are `gs`, in a module whose data layout is `l`. -/
def Global.initUnits (l : DataLayout) (gs : List Global) (g : Global) : Nat :=
  g.init.foldl (fun n p => n + p.unitCount l gs g.mem) 0

/-- A piece of an initializer fits in the memory `n` of a module whose data
layout is `l`, as an item of a table whose globals are `gs`: each unit it
gives is below `2^U`, for the memory's unit width `U`, and the global whose
address it gives is one of `gs`. -/
def InitPiece.Fits (l : DataLayout) (gs : List Global) (n : Nat) : InitPiece → Prop
  | .units us => ∀ u ∈ us, u < 2 ^ (l.entry n).unit
  | .zeros _ => True
  | .addr s _ => (Global.named? gs s).isSome

/-- A global is valid as an item of a table whose globals are `gs`, in a
module whose data layout is `l`: its numbers are within the limit, the module has its memory,
its alignment is valid, each piece of its initializer fits, and the
initializer takes no more than its size. -/
structure Global.Valid (l : DataLayout) (gs : List Global) (g : Global) : Prop where
  limits : g.InLimits
  memory : l.Declares g.mem
  align : MemLayout.ValidAlign g.align
  pieces : ∀ p ∈ g.init, p.Fits l gs g.mem
  size : g.initUnits l gs ≤ g.size

variable {d : Dialect}

/-- Each global of each symbol table of a module is valid in the module's
data layout, as an item of its own table. -/
def Module.GlobalsValid (m : Module d) : Prop :=
  ∀ t ∈ m.tables, ∀ g ∈ t.globals, g.Valid m.layout t.globals

end Fir
