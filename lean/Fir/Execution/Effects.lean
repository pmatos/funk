import Fir.Syntax.Module

/-!
The interpreter is written once, for every dialect, and it counts its steps
against a budget, its fuel (ADR-2026-10-29-2009). It does not fix how the
effects of ops are carried out. Each dialect states the effects its ops
need, and any way of running a program that provides those effects can run
its ops (ADR-2026-10-29-2009). The core dialect needs two, below: choosing
arbitrary bits, and immediate UB. Calls need a third, the call effect at the
end of this section, which the run itself provides, since a call shares the
run's fuel budget.

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
  /-- A NaN result of a float op in `float<e,mb>` chooses its sign and
  mantissa, `mb + 1` bits (ADR-2026-11-09-1549). It is a choice of `mb + 1`
  bits, and only a monad that walks the choices tells it apart, so that a
  walk can try a few NaNs where it cannot try them all. -/
  chooseNaN (e mb : Nat) : m (BitVec (mb + 1)) := choose (mb + 1)

/--
Immediate UB: `ub reason` ends the run with undefined behaviour, such as
branching on poison or dividing by zero. Unlike poison, it is not a value.
-/
class MonadUB (m : Type → Type) where
  ub {α : Type} : String → m α

/-!
# The semantics of an op

Each dialect gives its ops their meaning in one place, in the shape that
LeanMLIR gives it (ADR-2026-10-29-2009). An op that is not a terminator maps
its operand values to its result values. A terminator says where control
goes next.
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
  /-- `pick op ok args` is the symbol that `op`, an op whose callee is
  picked when it runs, calls on the operands `args`. The run gives it the
  test `ok`: `ok s` holds when the module has a function, or an external
  declaration, with the symbol `s` that takes the values the call passes
  and gives the call's results (#235). -/
  pick : (op : d.Op) → (Name → Bool) → HVector toType (sig op) → m Name

/-!
# The call effect

A call runs another function of the module, by its symbol, as `call @g`
does. It is an effect of the run, not one that a dialect provides, for two
reasons: an op's meaning sees only the op and its operands, not the module,
so it cannot find the callee; and all calls share the run's fuel budget,
which is the interpreter's (ADR-2026-10-29-2009). So a dialect does not give
a call a meaning of its own. It names the function that the op calls, and
the interpreter runs that function:

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

An op that calls no function runs by the meaning its dialect gives it. In
the core dialect, `call @g` calls `@g`, and no other op calls a function:
naming the callee of `call` is what gives `call` its meaning.

An op may instead call a function that its rule picks when it runs, as a
call through a pointer does (#235, the human's ruling of 2026-11-19, Q2).
Its rule, `pick`, sees all of its operands and maps them to a symbol; by
convention its first operand is the one that names the callee, and the rule
is UB when that operand names no function, or one whose signature is not
the call's. The call then runs as a call of that symbol does, with the op's
other operands as the callee's arguments. The rule is the dialect's, so UB stays in the
dialect's semantics, where every other UB is; the run only says where the
call starts and where it returns. Such an op takes two steps of fuel: one
for its rule, which picks the callee, as an op that runs by its own rule
does, and one for the call, which then runs as a call of a callee that an
op names does.
-/

/--
The callee of an op that calls a function: a symbol that the op names, as
`call @g` names `@g`, or one that the op's rule picks when it runs, from
the op's operands, as a call through a pointer does (#235). An op whose
callee is picked passes its operands but the first to the callee.
-/
inductive Callee where
  | fixed (s : Name)
  | picked
  deriving DecidableEq

/--
The ops of a dialect that call a function of the module: `callee? op` is
`op`'s callee, a symbol it names or one its rule picks, and `none` for an
op that calls none. The interpreter runs the callee with the fuel that the
caller has left. It asks `callee?` only of an op that is not a terminator: a
terminator runs through `exit`, whatever `callee?` says of it.

Nothing ties `callee?` to validation. The dialect's own validation rule
for a call must check that its callee is a function of the module and
that the types of its operands and results match the callee's signature,
as the core rule for `call` does.
-/
class DialectCall (d : Dialect) where
  callee? : d.Op → Option Callee
export DialectCall (callee?)

end Fir
