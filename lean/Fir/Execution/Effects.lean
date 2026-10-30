import Fir.Syntax.Dialect

/-!
The interpreter is a monadic definitional interpreter with fuel (S7,
ADR-2026-10-29-2009), written once against an abstract monad. It never names
a concrete monad. Each dialect states the effects its ops need as class
constraints on the monad, and a monad that has those effects can run them
(ADR-2026-10-29-2030). The core dialect needs two, below. Calls (#20) add an
effect that shares the fuel budget.

# Effects
-/

namespace Fir

/--
The choice effect (ADR-2026-10-29-2017): `choose w` gives `w` arbitrary bits.
`freeze` of poison calls it once, and every use of the frozen value then
sees the bits it chose.
-/
class MonadChoice (m : Type → Type) where
  choose : (w : Nat) → m (BitVec w)

/--
Immediate UB: `ub reason` ends the run with undefined behaviour, such as
branching on poison or dividing by zero. Unlike poison, it is not a value.
-/
class MonadUB (m : Type → Type) where
  ub {α : Type} : String → m α

/-!
# The semantics of an op

Each dialect gives its ops their meaning through one class, in the shape of
LeanMLIR's `DialectDenote` (ADR-2026-10-29-2030). An op that is not a
terminator maps its operand values to its result values. A terminator says
where control goes next.
-/

/--
Where control goes when a block ends: to the terminator's successor with this
index, or back to the caller, returning the terminator's operands. It may
grow, for example for unwinding.
-/
inductive Exit where
  | goto (succ : Nat)
  | ret
  deriving Repr, DecidableEq

/--
The semantics of a dialect's ops, in a monad `m` that has the effects the
dialect needs.

* `denote` runs an op that is not a terminator. It takes one value of each
  operand type and gives one value of each result type.
* `exit` runs a terminator and says where control goes. The values passed to
  a successor are its successor arguments, and a return returns the
  terminator's operands.

Validation guarantees that an op is only ever given values of its operand
types.
-/
class DialectDenote (d : Dialect) [TyDenote d.Ty] [DialectSignature d]
    (m : Type → Type) where
  denote : (op : d.Op) → HVector toType (sig op) → m (HVector toType (returnTypes op))
  exit : (op : d.Op) → HVector toType (sig op) → m Exit

end Fir
