import Fir.Syntax.Dialect
import Fir.Syntax.Global

/-!
The layout of an aggregate is an item that describes memory, not a value
(ADR-2026-11-09-1550, ADR-2026-11-16-1546): a size, an alignment and a list
of fields, each at an offset, all counted in the units of one memory. A
module's items hold the layouts (`Fir.Item`); validation and the text read
them there. Every number of a layout, and of a global, has the same limit,
`2^64 - 1`, so that the text can write it.
-/

namespace Fir

variable {d : Dialect}

/--
A field of an aggregate's layout (ADR-2026-11-09-1550): its offset, in
units of the layout's memory, and its type, a scalar. A repeated field,
`count = some c`, is an array of `c` elements of the type, each element
rounded up to the type's alignment (the human's ruling of 2026-11-16 on
#236); a field with `count = none` is one value of the type, and has no
elements.
-/
structure Field (d : Dialect) where
  offset : Nat
  ty : d.Ty
  count : Option Nat := none

/--
The layout of an aggregate (ADR-2026-11-09-1550, ADR-2026-11-16-1546): an
item that names a size, an alignment and a list of fields, each at an
offset, all counted in the units of the memory `mem` that the layout
describes. A layout is not a type: no value has it, and an op reads it by
its symbol.
-/
structure Aggregate (d : Dialect) where
  name : String
  mem : Nat
  size : Nat
  align : Nat
  fields : List (Field d)

/-- Every type that an aggregate's layout states: the type of each field. -/
def Aggregate.types (a : Aggregate d) : List d.Ty := a.fields.map (·.ty)

/-- The largest number that an aggregate's layout may hold, `2^64 - 1`: its
memory, size, alignment, and each field's offset and count. -/
def Aggregate.limit : Nat := 2 ^ 64 - 1

/-- The numbers of an aggregate's layout are within the limit. -/
def Aggregate.InLimits (a : Aggregate d) : Prop :=
  a.mem ≤ Aggregate.limit ∧ a.size ≤ Aggregate.limit ∧ a.align ≤ Aggregate.limit ∧
    ∀ f ∈ a.fields, f.offset ≤ Aggregate.limit ∧ ∀ c ∈ f.count, c ≤ Aggregate.limit

/-- A piece of an initializer is within the limit of the numbers of an
aggregate's layout, `2^64 - 1`: its count of zeros and its offset. A unit
has no limit here: validation bounds it by its memory's unit width. -/
def InitPiece.InLimits : InitPiece → Prop
  | .units _ => True
  | .zeros n => n ≤ Aggregate.limit
  | .addr _ k => k ≤ Aggregate.limit

/-- The numbers of a global are within the limit: its memory, size and
alignment, and each piece of its initializer. -/
def Global.InLimits (g : Global) : Prop :=
  g.mem ≤ Aggregate.limit ∧ g.size ≤ Aggregate.limit ∧ g.align ≤ Aggregate.limit ∧
    ∀ p ∈ g.init, p.InLimits

end Fir
