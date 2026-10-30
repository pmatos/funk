/-!
Every op has a location: where it came from (H8, ADR-2026-10-29-2013). The
field is required; `unknown` is a valid value. Locations are erased before
semantics: no rule of validation or execution reads them, so they never
change what a program means. Parsers and printers keep them, and round trips
preserve them.

An op does not hold its location directly. It holds a _location reference_,
a number, and the module's _location table_ gives the location that each
number stands for. In text, the reference is written `@N` at the end of the
op, and the table is the `locs { ... }` block that ends the module. Ops that
share a location share one entry, which keeps op lines short.
-/

namespace Fir

/--
A location reference: the key of an entry in the module's location table,
written `@N` in text. The numbers are the producer's: they are stored and
printed as given, never renumbered.
-/
abbrev LocRef := Nat

/--
A location. Every kind except `unknown` and `range` is built from other
entries of the location table, by reference.

* `unknown`: nothing is known about where the op came from.
* `range file l₁ c₁ l₂ c₂`: a range of source text in `file`, from line `l₁`,
  column `c₁` to line `l₂`, column `c₂`, as MLIR writes it. Lines count from
  1. Columns count UTF-8 bytes from 1, and column 0 means that the column is
  unknown. The end is exclusive: it is the position just after the range's
  last byte, so a range whose end equals its start is empty.
* `name n`: a name, such as the source variable an op computes.
* `callsite callee caller`: the op came from inlining. `callee` is its
  location in the inlined function, `caller` the location of the call.
* `fused locs`: the op stands for two or more ops, such as the result of
  merging them, and `locs` are their locations.
* `derived src`: a transformation made the op from the op at `src`, such as
  when a pass expands one op into several.
-/
inductive Location where
  | unknown
  | range (file : String) (startLine startCol endLine endCol : Nat)
  | name (n : String)
  | callsite (callee caller : LocRef)
  | fused (locs : List LocRef)
  | derived (src : LocRef)
  deriving Repr, DecidableEq, Inhabited

/--
The location table of a module: entries from a reference to a location, in
the order of their references.
-/
abbrev LocTable := List (LocRef × Location)

/-- The references that a location is built from. -/
def Location.refs : Location → List LocRef
  | .unknown | .range .. | .name _ => []
  | .callsite callee caller => [callee, caller]
  | .fused locs => locs
  | .derived src => [src]

/-- The numbers that a location holds: its lines and columns, or its
references. -/
def Location.numbers : Location → List Nat
  | .range _ l₁ c₁ l₂ c₂ => [l₁, c₁, l₂, c₂]
  | l => l.refs

/--
Location references, lines and columns are below `2^32`, so that every
implementation can hold them in 32 bits (N3). The text format rejects a
larger one, and validation rejects a table that holds one.
-/
def Location.limit : Nat := 2 ^ 32

end Fir
