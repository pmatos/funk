import Fir.Core.Values

/-!
# Calls

Ticket #20 gives `call` its rule. `call @g` runs the function of the
module whose symbol is `@g`, the caller itself included, so a function
may call itself, and two functions may call each other. A symbol that is
not a word is quoted in text: `call @"1"` calls the function `@"1"`, and
`@1` is always a location reference.

A call is not computed by a rule of its own. Its meaning is the run of its
callee, which the interpreter runs as the call effect of the effects
section (ADR-2026-11-02-0836). The core dialect says only which function
each op calls: `Op.callTarget?` names the symbol of `call @g`, `g`, and no
other core op calls one. The instance `DialectCall CoreDialect`, in the
core op semantics, sends each op there. A call then runs so:

* _Arguments and results._ The call's operands are the callee's arguments,
  in order, and the values that the callee returns are the call's results,
  any number of each, none included (ADR-2026-10-30-0816). Validation's
  rule for `call @g`, in the core rules, asks that `@g` is a function of
  the module whose parameter types are the call's operand types and whose
  result types are the call's result types. So a call in a valid module
  always finds its callee, and passes and receives values of the right
  types.
* _Poison passes through, both ways._ `call` is an exception to poison
  propagation that passes values on as they are (ADR-2026-10-30-0818). A
  poison operand is a poison argument: the callee sees poison, and
  whatever it does with it, the call does. A poison that the callee
  returns is a poison result of the call. A poison argument does not make
  every result poison: a callee may ignore it, or `freeze` it.
* _UB._ UB in the callee is UB of the caller: the run ends there, with the
  callee's reason, and nothing after the call runs.
* _Fuel._ The call takes one step of fuel, as every op does, and its
  callee runs with the steps that the caller has left. The caller goes on
  with the steps that the callee leaves, so a caller and all its callees
  share one budget. A run that recurses without end runs out of fuel at
  every budget: it diverges, as a loop that never ends does.

# The stand-in in the set monad

The op-level obligations of the poison classes section, totality
(`OpTotal`) and monotonicity (`OpMonotone`), look at an op's `denote` in
the set monad, and `LawfulDialectPoison` asks them of every op. The set
monad has no module, so a `denote` cannot run a callee: `call`'s `denote`
can only be a stand-in, `callStandIn`. The interpreter never runs it,
since it runs the callee of every op that has one, and `fir-ref` never
reports it.

The stand-in is immediate UB, on every operand vector
(ADR-2026-11-02-1156). UB allows every behaviour, so every way that a
call may end, whatever its callee, refines it. It has an outcome on every
op instance, even one with a result type that has no values, such as
`ptr`, and it is monotone, since UB on the original operands allows
whatever happens on refined ones. So it claims nothing about calls: its
obligations hold, and say nothing of how a call behaves. The facts about calls are stated about the runs of functions:
progress and no stuck path with calls and recursion (the section on every
valid core function), and their refinement theorems, #20's next stage. An
op _without_ rules is never UB in the spec (ADR-2026-10-30-1855), because
`fir-ref` would report that UB as the op's meaning. `call` has rules, its
callee's, and `fir-ref` never reaches its stand-in.
-/

namespace Fir.Core

/-- The function that a core op calls: `call @g` calls `@g`, and no other
core op calls one. -/
def Op.callTarget? : Op → Option Name
  | .call g _ _ => some g
  | _ => none

/-- The reason of `call`'s stand-in UB. No run reports it: the interpreter
runs a call's callee instead. -/
def callStandInReason : String := "call's stand-in, which the interpreter never runs"

/-- `call`'s stand-in in any monad with the UB effect, the `denote` that
the op-level obligations look at: immediate UB on every operand vector,
which every behaviour of a call refines. -/
def callStandIn {m : Type → Type} [MonadUB m] {ts rs : List Ty} :
    HVector toType ts → m (HVector toType rs) :=
  fun _ => MonadUB.ub callStandInReason

end Fir.Core
