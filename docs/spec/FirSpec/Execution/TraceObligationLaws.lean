import VersoManual
import Fir.Execution.TraceObligationLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on ops monotone in the traced layer, which renders
`Fir.Execution.TraceObligationLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Ops monotone in the traced layer: readable blocks" =>

:::moduleDocs (fingerprint := "2795909418977133827")
:::

:::readable Fir.TraceEnd.trace_mapActs Fir.TraceEnd.Allows.mapActs Fir.TraceRefinedBy.step (fingerprint := "6627922759765765824")
*Theorems: the step before an op.* Mapping the acts of a way of ending maps
its trace. Mapping each act $`a` to the act $`\mathsf{act}~a` of a marked
trace keeps one way of ending allowing another. So a computation that
refines another still does after a step $`\mathsf{tick}`, its acts mapped
so: UB after the acts $`t` becomes UB after $`\mathsf{tick}` and $`t`.
:::

:::readable Fir.OpTraceMonotone.stepAt Fir.OpTracePickMonotone.stepAt Fir.Func.TraceOpsMonotone.stepAt (fingerprint := "16363967305923345560")
*Theorems: monotone in the traced layer of marked traces.* An op monotone
by its dialect's rule in the traced layer, at $`\ell`, $`\rho` and $`L`, is
monotone in the traced layer of marked traces, where it runs after a step.
So is the external-call rule, and each op of a function whose ops are.
So does a rule to pick a callee, which runs after its step.
:::

:::readable Fir.ExtTraceMonotone.stepAt Fir.ExtTraceMonotone.ofLift (fingerprint := "2461249291503010545")
*Theorems: the external-call rule, monotone.* An external-call rule
monotone in the traced layer, at $`\ell`, $`\rho` and $`L`, is monotone in
the traced layer of marked traces, where it runs after a step. An
external-call rule that lifts the rule with memory, UB, is monotone in the
traced layer: it ends only in UB that shows no act.
:::

:::readable Fir.TraceRefinedBy.liftMem (fingerprint := "2252719804679232894")
*Theorem: the lift keeps refinement.* Computations of the state layer that
refine each other, lifted onto the memories of the traced state, refine
each other in the traced layer: the lift shows nothing and keeps what
escaped, so results, memories and UB keep their refinement.
:::

:::readable Fir.OpLiftsMem Fir.OpLiftsMem.ofMem Fir.LiftsMem.opLiftsMem (fingerprint := "17184973681218294442")
*Definition: an op that lifts its rule with memory.* At $`\ell`, $`\rho`
and $`L`, the op $`op` lifts its rule with memory in a dialect's traced
semantics when, on every operands $`\vec{v}`, its traced rule is its rule
with memory, lifted onto the memories of the traced state, as an op that is
not a terminator and as a terminator, and its rule to pick a callee, for
every test of the symbols a run can call:

$$`\mathrm{trace}(op)(\vec{v}) = \mathrm{lift}(\mathrm{mem}(op)(\vec{v}))`

It shows no event and keeps what escaped. Every op of a dialect whose ops
show no event lifts its rule, and so does every op of a dialect whose
traced semantics lifts its semantics with memory. A dialect may show events
by other rules, as the core does by its external calls, while each of its
ops lifts its rule.
:::

:::readable Fir.OpTraceMonotone.ofLift Fir.OpTracePickMonotone.ofLift Fir.OpTraceMonotone.ofMem Fir.Func.TraceOpsMonotone.ofLift Fir.Func.TraceOpsMonotone.ofMem (fingerprint := "8373069733619326865")
*Theorems: ops that lift their rule are monotone.* An op that lifts its rule
with memory, and is monotone with memory, is monotone in the traced layer.
An external-call rule that is the lift of the rule with memory, UB, is
monotone too. So each op of a function whose ops are monotone with memory
is monotone in the traced layer, in a dialect whose ops each lift their
rule and whose external-call rule is that lift. In particular, in the traced
semantics of a dialect whose ops show no event.
A rule to pick a callee that lifts its rule with memory, and is monotone
with memory, is monotone in the traced layer.
:::
