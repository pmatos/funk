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

:::moduleDocs (fingerprint := "14664865824699207852")
:::

:::readable Fir.TraceEnd.trace_mapActs Fir.TraceEnd.Allows.mapActs Fir.TraceRefinedBy.step (fingerprint := "6627922759765765824")
*Theorems: the step before an op.* Mapping the acts of a way of ending maps
its trace. Mapping each act $`a` to the act $`\mathsf{act}~a` of a marked
trace keeps one way of ending allowing another. So a computation that
refines another still does after a step $`\mathsf{tick}`, its acts mapped
so: UB after the acts $`t` becomes UB after $`\mathsf{tick}` and $`t`.
:::

:::readable Fir.OpTraceMonotone.stepAt Fir.Func.TraceOpsMonotone.stepAt (fingerprint := "10351722494700514947")
*Theorems: monotone in the traced layer of marked traces.* An op monotone
by its dialect's rule in the traced layer, at $`\ell`, $`\rho` and $`L`, is
monotone in the traced layer of marked traces, where it runs after a step.
So is each op of a function whose ops are.
:::

:::readable Fir.TraceRefinedBy.liftMem Fir.OpTraceMonotone.ofMem Fir.Func.TraceOpsMonotone.ofMem (fingerprint := "5519996737546212163")
*Theorems: the lift of the semantics with memory.* Computations of the
state layer that refine each other, lifted onto the memories of the traced
state, refine each other in the traced layer: the lift shows nothing and
keeps what escaped, so results, memories and UB keep their refinement. In
the traced semantics of a dialect whose ops show no event, an op monotone
with memory is monotone in the traced layer, and so is each op of a
function whose ops are monotone with memory.
:::
