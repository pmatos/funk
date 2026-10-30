/-!
fir is built from dialects (G0, ADR-2026-10-29-2016). A dialect supplies its
types and its ops, and the rest of the spec is written once for every
dialect. Nothing in fir is a closed list of all ops or all types: the core
dialect of M0 is one instance of the classes below, and an extension dialect
for a GPU or a quantum processor would be another.

The classes keep the shape of LeanMLIR's (ADR-2026-10-29-2030), so that the
semantics of one op ports between the two mechanically. The terms that use
them are fir's own, and are extrinsically typed: a value is referred to by
its name, and typing is a separate validation judgement.
-/

namespace Fir

/--
A heterogeneous vector: one value for each type in a list. Operand and result
values travel in one, as in LeanMLIR.
-/
inductive HVector {α : Type} (f : α → Type) : List α → Type where
  | nil : HVector f []
  | cons {a : α} {as : List α} : f a → HVector f as → HVector f (a :: as)

/--
A dialect: its ops and its types.

An op of a dialect is an op _instance_. It carries its attributes and every
type it is used at, so that its operand and result types are a function of
the op alone. The core dialect's `add` at `i32` with the `nsw` flag is one
op, and `add` at `i64` is another.

Unlike LeanMLIR, a dialect does not fix a monad. Its semantics states the
effects it needs as class constraints on the interpreter's monad (see the
execution chapter).
-/
structure Dialect where
  /-- The dialect's op instances. -/
  Op : Type
  /-- The dialect's types. -/
  Ty : Type

/--
The meaning of a dialect's types: each type `t` denotes the Lean type of its
values, written `⟦t⟧`.
-/
class TyDenote (Ty : Type) where
  /-- The Lean type of the values of a type. -/
  toType : Ty → Type
export TyDenote (toType)

@[inherit_doc] notation "⟦" x "⟧" => TyDenote.toType x

/--
The signature of each op of a dialect.

`sig` gives the types of the op's operands and `returnTypes` the types of its
results. `isTerminator` marks the ops that end a block, and `succCount` says
how many successors an op has: a terminator chooses one of them, or returns.
Only terminators have successors.

Region signatures and effect kinds come later, with the first dialect whose
ops have regions (H6) or need effect classes (H7).
-/
class DialectSignature (d : Dialect) where
  /-- The types of the op's operands. -/
  sig : d.Op → List d.Ty
  /-- The types of the op's results. -/
  returnTypes : d.Op → List d.Ty
  /-- Whether the op ends a block. -/
  isTerminator : d.Op → Bool
  /-- How many successors the op has. -/
  succCount : d.Op → Nat
export DialectSignature (sig returnTypes isTerminator succCount)

end Fir
