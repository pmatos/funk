import VersoManual
import Fir.Execution.TraceFinite
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on ops of finitely many outcomes, given the world's answers, which renders
`Fir.Execution.TraceFinite` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Ops of finitely many outcomes, given the world's answers: readable blocks" =>

:::moduleDocs (fingerprint := "4526681264093363768")
:::

:::readable Fir.Act.Agrees Fir.Act.Agrees.of_prefix Fir.Act.agrees_append Fir.Act.Agrees.of_isRefinedPrefix (fingerprint := "14362968264670860557")
*Definition: answers by position.* An answer stream $`\alpha` gives, at
each place $`i`, an answer or none. The trace $`t` agrees with $`\alpha`
when $`\alpha(i) = \mathrm{answer}(t_i)` at each place $`i` of $`t`.

*Theorems.* A trace that starts one that agrees with $`\alpha` agrees with
it. $`t \mathbin{+\!\!+} t'` agrees with $`\alpha` exactly when $`t` does
and $`t'` agrees with $`\alpha` after the places of $`t`. A trace refined
by a prefix of one that agrees with $`\alpha` agrees with it, since
refinement of acts keeps their answers.
:::

:::readable Fir.TraceFinitelyMany Fir.StepFinitelyMany Fir.Step.actsOf_flatMap_act Fir.TraceFinitelyMany.step Fir.FinitelyMany.liftMem (fingerprint := "467898124999996319")
*Definition: finitely many outcomes, given the world's answers.* A
computation $`c` of the traced layer has finitely many outcomes when, from
each traced state $`s` and for each answer stream $`\alpha`, the results
$`(a, t, s')` it may end with, whose acts $`t` agree with $`\alpha`, lie in
one finite list. UB is not counted. In the traced layer of marked traces,
the acts of each marked trace must agree.

*Theorems.* The acts of a trace, each mapped to the act of a marked trace,
are the trace. A computation with finitely many outcomes still has after a
step. A computation with finitely many outcomes with memory, lifted onto
the memories of the traced state, has finitely many in the traced layer.
:::

:::readable Fir.TraceFinitelyMany.ub (fingerprint := "17828076345672588217")
*Theorem.* UB has finitely many outcomes, given the world's answers: its
only one, UB with an empty trace.
:::

:::readable Fir.OpsTraceFinite Fir.OpsStepFinite Fir.OpsOneStep Fir.TraceM.step_ticks (fingerprint := "8100468544612697770")
*Definition: the hypothesis.* $`\mathrm{OpsTraceFinite}`: every op that
runs by its own rule, a terminator or an op with no callee, has finitely
many outcomes in the traced layer, given the world's answers, on every
operands, as an op that is not a terminator and as a terminator, and so
does every external call, at every symbol, arguments and result types, and
the rule of every op that picks its callee, whatever the run says it can
call. $`\mathrm{OpsStepFinite}` is the same in the traced layer of marked
traces. $`\mathrm{OpsOneStep}`: every path of every op, of every external
call and of every rule that picks a callee shows exactly one step.

*Theorem.* After a step, each act of its traces an act of the marked trace,
every path of a computation shows exactly one step.
:::

:::readable Fir.DialectTrace.stepAt_oneStep Fir.OpsTraceFinite.stepAt (fingerprint := "8481470131927335375")
*Theorems: the step keeps the hypothesis.* In the traced layer of marked
traces, at $`\ell`, $`\rho` and $`L`, every path of every op and of every
external call shows exactly one step, and ops and external calls with
finitely many outcomes by the dialect's rules have finitely many there.
:::

:::readable Fir.OpsTraceFinite.ofLift Fir.OpsTraceFinite.ofMem (fingerprint := "9371961871677821393")
*Theorem: ops that lift their rule have finitely many outcomes.* In a
dialect whose ops each lift their rule with memory, and whose external-call
rule is its rule with memory, UB, lifted, ops of finitely many outcomes
with memory have finitely many in the traced layer, given the world's
answers: the lift shows nothing and keeps what escaped, and UB is one
outcome. In
particular, in the traced semantics of a dialect whose ops show no event.
:::
