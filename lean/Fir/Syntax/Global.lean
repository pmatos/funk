/-!
A global is an item that names a block of units of one memory, live for
the whole run, with its first contents (ADR-2026-11-09-1546). It holds no
fir value and states no type: its initializer is units and addresses, as
an assembler writes data and relocations. A module's items hold its
globals (`Fir.Item`); validation and the text read them there. A symbol is
written without its `@`, as every name of a module is.
-/

namespace Fir

/-- A global's linkage (ADR-2026-11-09-1546): `internal`, the default, is
seen only by the module; `exported` is written `export`, and code that funk
did not compile sees it too. Weak, common and visibility linkage wait for
the C frontend. -/
inductive Linkage where
  | internal
  | exported
  deriving Repr, DecidableEq

/-- A piece of a global's initializer (ADR-2026-11-09-1546), which fills the
global's units in order from its first: units given one by one, each as the
number its bits write; `n` zero units; or the address of the global `@s`
plus `k` units, which takes the units of one pointer of `@s`'s memory. -/
inductive InitPiece where
  | units (us : List Nat)
  | zeros (n : Nat)
  | addr (sym : String) (offset : Nat)
  deriving Repr, DecidableEq

/--
A global (ADR-2026-11-09-1546): an item that names a block of `size` units
of the memory `mem`, aligned to `align` units, with its initial units, a
flag that makes it constant, and its linkage. A global holds no fir value
and states no type: its initializer is units and addresses, as an
assembler writes data and relocations.
-/
structure Global where
  name : String
  mem : Nat
  size : Nat
  align : Nat
  const : Bool
  linkage : Linkage
  init : List InitPiece
  deriving Repr, DecidableEq

end Fir
