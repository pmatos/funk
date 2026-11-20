import VersoManual
import Fir.Execution.TraceObligations
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on monotonicity in the traced layer, which renders
`Fir.Execution.TraceObligations` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Monotonicity in the traced layer: readable blocks" =>

:::moduleDocs (fingerprint := "9425960177402715745")
:::

:::readable Fir.Step.IsRefinedBy (pin := Fir.instHRefinementStep) (fingerprint := "9259369860302064242")
*Definition: refined marked traces.* An element of a marked trace is
refined by another when both are a step $`\mathsf{tick}`, or both are acts
and the second refines the first. Marked traces refine one another element
by element.
:::

:::readable Fir.List.IsRefinedPrefix Fir.List.isRefinedBy_append Fir.List.isRefinedPrefix_nil Fir.List.IsRefinedPrefix.append_left Fir.List.IsRefinedPrefix.append_right (fingerprint := "4099428677081364833")
*Definition: a refined prefix.* The list $`l` is a refined prefix of $`l'`
when $`l'` starts with a list $`m` such that $`l \sqsubseteq m`, element by
element. The empty list is one of every list.

*Theorems.* Lists that refine element by element, appended, refine element
by element. So a refined prefix stays one after both lists are preceded by
lists that refine element by element, and after the second is followed by
any list.
:::

:::readable Fir.Step.actsOf_isRefinedBy Fir.Step.flatMap_act_isRefinedBy Fir.Step.actsOf_isRefinedPrefix Fir.Step.flatMap_act_isRefinedPrefix (fingerprint := "1381288009081559903")
*Theorems: acts and refined marked traces.* When $`m \sqsubseteq m'`, then
$`\mathrm{acts}(m) \sqsubseteq \mathrm{acts}(m')`; when $`m` is a refined
prefix of $`m'`, so is $`\mathrm{acts}(m)` of $`\mathrm{acts}(m')`. Mapping
each act $`a` to the act $`\mathsf{act}~a` of a marked trace keeps
refinement and refined prefixes.
:::

:::readable Fir.TraceState.isRefinedBy_refl Fir.TraceState.IsRefinedBy.enter Fir.TraceState.IsRefinedBy.exit (pin := Fir.instHRefinementTraceState) (fingerprint := "16439252411456698260")
*Definition: refined traced states.* A traced state $`\langle S, E\rangle`
is refined by $`\langle S', E'\rangle` when $`S \sqsubseteq S'` and
$`E = E'`: the same allocations escaped, in the same order, so the world
names each by the same handle.

*Theorems.* A traced state refines itself, and entering or leaving a frame
keeps refinement.
:::

:::readable Fir.TraceEnd.trace Fir.TraceEnd.trace_after (fingerprint := "4406253799945635138")
*Definition: the trace of a way of ending.* A way of ending of the traced
layer, with a result or with UB, shows a trace. After the trace $`t`, it
shows $`t` first.
:::

:::readable Fir.TraceEnd.Allows Fir.TraceEnd.Allows.of_ub Fir.TraceEnd.Allows.after (fingerprint := "3795596474351469140")
*Definition: one way of ending allows another.* By the relation $`r` on
what they give, a way of ending of the source allows one of the target
when:

* both end with a result, $`(a, t, s)` and $`(b, t', s')`, with
  $`r(a, b)`, $`t \sqsubseteq t'` and $`s \sqsubseteq s'`; or
* the source hits UB after the acts $`t`, and $`t` is a refined prefix of
  the target's trace, whatever the target then does.

A result never allows UB.

*Theorems.* UB after no act allows every way of ending, and a way of
ending that allows another still does after traces that refine each
other.
:::

:::readable Fir.TraceRefinedBy (fingerprint := "12710899466537093517")
*Definition: a traced computation refined by another.* By the relation
$`r`, $`c'` refines $`c` when, from traced states $`s \sqsubseteq s'`,
each way that $`c'` may end from $`s'` is allowed by a way that $`c` may
end from $`s`.
:::

:::readable Fir.OpTraceMonotone Fir.TraceMonotoneOps Fir.Func.TraceOpsMonotone Fir.Func.TraceOpsMonotone.enter Fir.Func.TraceOpsMonotone.jump (fingerprint := "5633577407960804927")
*Definition: an op monotone in the traced layer.* In a semantics in the
traced layer, an op is monotone when, on operands
$`\vec{v} \sqsubseteq \vec{v}'`, what it runs by its own rule on
$`\vec{v}'` refines what it runs on $`\vec{v}`: an op that is not a
terminator, by refinement of its results; a terminator, by going to the
same place. The ops of a list, or of a function's blocks, are monotone
when each that runs by its own rule, a terminator or an op with no callee,
is.

*Theorems.* A run of such a function starts, and jumps, to the ops of one
of its blocks, all monotone.
:::
