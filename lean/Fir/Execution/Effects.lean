import Fir.Syntax.Module

/-!
The interpreter is a monadic definitional interpreter with fuel (S7,
ADR-2026-10-29-2009), written once against an abstract monad. It never names
a concrete monad. Each dialect states the effects its ops need as class
constraints on the monad, and a monad that has those effects can run them
(ADR-2026-10-29-2030). The core dialect needs two, below. Calls need a third,
the call effect at the end of this section, which the run itself provides,
since a call shares the run's fuel budget.

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

The interpreter gives an op only values of its operand types: it checks
each operand's type before it calls `denote` or `exit`, and the path is
stuck when one does not match, which validation rules out.
-/
class DialectDenote (d : Dialect) [TyDenote d.Ty] [DialectSignature d]
    (m : Type → Type) where
  denote : (op : d.Op) → HVector toType (sig op) → m (HVector toType (returnTypes op))
  exit : (op : d.Op) → HVector toType (sig op) → m Exit

/-!
# The call effect

A call runs another function of the module, by its symbol, as `call @g`
does (#20). It is an effect of the run, not of the monad, for two reasons:
`denote` sees only the op and its operands, not the module, so it cannot
find the callee; and all calls share the run's fuel budget, which is the
interpreter's (ADR-2026-11-02-0836). So a dialect does not give a call its
meaning through `denote`. It names the function that the op calls, and the
interpreter runs that function:

* the call's operands are the callee's arguments, and the values that the
  callee returns are the call's results;
* the call takes one step of fuel, as every op does. The callee then runs
  with the steps that the caller has left, and gives back the steps it
  leaves; the caller goes on with those. So every step of a callee is
  charged to its caller's budget, and a run that recurses without end runs
  out of fuel;
* UB in the callee is UB of the caller, a callee that runs out of fuel
  ends the whole run so, and a callee that is stuck leaves its caller
  stuck.

An op that calls no function runs through `denote`. In the core dialect,
`call @g` calls `@g`, and no other op calls a function: ticket #20 names
the callee of `call`, and so gives `call` its meaning.
-/

/--
The ops of a dialect that call a function of the module: `callee? op` is the
symbol of the function that `op` calls, and `none` for an op that calls
none. The interpreter runs the callee with the fuel that the caller has
left. It asks `callee?` only of an op that is not a terminator: a
terminator runs through `exit`, whatever `callee?` says of it.

Nothing ties `callee?` to validation. The dialect's own validation rule
for a call must check that its callee is a function of the module and
that the types of its operands and results match the callee's signature,
as the core rule for `call` does.
-/
class DialectCall (d : Dialect) where
  callee? : d.Op → Option Name
export DialectCall (callee?)

end Fir
