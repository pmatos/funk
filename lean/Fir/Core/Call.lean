import Fir.Core.Values

/-!
# Calls

Ticket #20 gives `call` its meaning. `call @g` runs the function of the
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

# No rule at op level

A call has no rule of its own in the set monad: `Op.denote?` gives `none`
for `call`, and its `denote` there has no outcome. The interpreter never
looks at it, since it runs the callee of every op that has one before it
looks at `denote`, and `fir-ref` never reaches it. Its meaning is its
callee's run, and nothing else.

So `call` has no op-level obligation (ADR-2026-11-02-1514). The poison
obligations of the poison classes section ask totality (`OpTotal`) and
monotonicity (`OpMonotone`) only of the ops that the interpreter runs by
their own rule: terminators, and ops with no callee. The set monad has no
module, so a rule there cannot run a callee. Any rule for `call` there
would be a stand-in with a meaning that a call does not have, such as
immediate UB, and obligations met by a stand-in would say nothing about
calls. A stand-in that is UB would also be refined by every computation,
so a statement that reads it as a source, such as a rewrite rule proved
op by op, would hold for every rewrite of a call. Such statements leave
out the ops with a callee, as the obligations do; M2's rewrite rules will
too (#96).

The facts about calls are stated about the runs of functions instead,
for every function of every valid core module, calls and recursion
included: fuel monotonicity, progress and no stuck path
(`Core.fuelMonotone`, `Core.progress`, `Core.neverStuck`, in the section
on every valid core function), and refinement through a call, for
refined arguments and for a replaced callee (`Core.args_isRefinedBy`,
`Core.replaceBody_isRefinedBy`, in the section on refinement through core
calls).
-/

namespace Fir.Core

/-- The function that a core op calls: `call @g` calls `@g`, and no other
core op calls one. -/
def Op.callTarget? : Op → Option Name
  | .call g _ _ => some g
  | _ => none

end Fir.Core
