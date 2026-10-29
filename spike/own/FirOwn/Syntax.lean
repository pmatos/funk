/-!
# Abstract syntax, parameterized over a dialect

The classes copy the shape of LeanMLIR's (`Dialect`, `DialectSignature`,
`TyDenote`, `DialectDenote`, `HVector`), so per-op semantics port between the
two unchanged. The terms differ on purpose: fir's syntax is extrinsically
typed. Values have names, ops have locations, and a function is a CFG of
blocks with arguments. Typing is a separate validation judgement.
-/

namespace FirOwn

/-- A heterogeneous vector, as in LeanMLIR. -/
inductive HVector {α : Type} (f : α → Type) : List α → Type where
  | nil : HVector f []
  | cons {a : α} {as : List α} : f a → HVector f as → HVector f (a :: as)

/-- A dialect supplies its ops and its types (G0). Unlike LeanMLIR, it does
not fix a monad: each dialect states the effects it needs as typeclass
constraints on the interpreter's monad. -/
structure Dialect where
  Op : Type
  Ty : Type

/-- The meaning of a dialect's types. -/
class TyDenote (Ty : Type) where
  toType : Ty → Type
export TyDenote (toType)

notation "⟦" x "⟧" => TyDenote.toType x

/-- Operand and result types of each op, and whether it ends a block. -/
class DialectSignature (d : Dialect) where
  sig : d.Op → List d.Ty
  returnTypes : d.Op → List d.Ty
  isTerminator : d.Op → Bool
export DialectSignature (sig returnTypes isTerminator)

/-- Where control goes when a block ends: to one of the op's successors, or
back to the caller with the op's operands. -/
inductive Exit where
  | goto (succ : Nat)
  | ret

/-- The semantics of a dialect's ops, in any monad `m` that has the effects
the dialect needs. `denote` has the same type as LeanMLIR's
`DialectDenote.denote` (fir's M0 ops have no regions). -/
class DialectDenote (d : Dialect) [TyDenote d.Ty] [DialectSignature d]
    (m : Type → Type) where
  denote : (op : d.Op) → HVector toType (sig op) → m (HVector toType (returnTypes op))
  exit : (op : d.Op) → HVector toType (sig op) → m Exit

abbrev Name := String

/-- A source location (H8), simplified to the `@N` reference into the
module's `locs` table. Locations are erased before semantics. -/
inductive Loc where
  | unknown
  | ref (n : Nat)
  deriving Repr, DecidableEq

/-- A successor of a terminator: a block and the values passed to its
arguments (H1). -/
structure Succ where
  block : Name
  args : List Name
  deriving Repr, DecidableEq

/-- One op in a block. Every op of every dialect has this one shape (G0):
named results with types, the dialect op (which carries its attributes),
operands, successors and a location. -/
structure Inst (d : Dialect) where
  results : List (Name × d.Ty)
  op : d.Op
  args : List Name
  succs : List Succ := []
  loc : Loc := .unknown

/-- A block: a label, typed arguments, and ops ending in a terminator. -/
structure Block (d : Dialect) where
  label : Name
  params : List (Name × d.Ty)
  body : List (Inst d)

/-- A function is a region isolated from above (H2): nothing in it refers to
a value outside it. The entry block's arguments are the parameters. -/
structure Func (d : Dialect) where
  name : Name
  results : List d.Ty
  blocks : List (Block d)

end FirOwn
