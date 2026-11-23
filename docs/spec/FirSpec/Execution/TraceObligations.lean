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

:::moduleDocs (fingerprint := "4445902941565328772")
:::

:::readable Fir.Step.IsRefinedBy (pin := Fir.instHRefinementStep) (fingerprint := "12649089963462645072")
*Definition: refined marked traces.* An element of a marked trace is
refined by another when both are a step $`\mathsf{tick}`, or both are acts
and the second refines the first. Marked traces refine one another element
by element.
:::

:::readable Fir.List.IsRefinedPrefix Fir.List.isRefinedPrefix_nil Fir.List.IsRefinedPrefix.append_left Fir.List.IsRefinedPrefix.append_right (fingerprint := "927429146959535312")
*Definition: a refined prefix.* The list $`l` is a refined prefix of $`l'`
when $`l'` starts with a list $`m` such that $`l \sqsubseteq m`, element by
element. The empty list is one of every list.

*Theorems.* A refined prefix stays one after both lists are preceded by
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

:::readable Fir.TraceState.isRefinedBy_refl Fir.TraceState.isRefinedBy_trans Fir.TraceState.IsRefinedBy.enter Fir.TraceState.IsRefinedBy.exit (pin := Fir.instHRefinementTraceState) (fingerprint := "12969031787064880444")
*Definition: refined traced states.* A traced state $`\langle S, E\rangle`
is refined by $`\langle S', E'\rangle` when $`S \sqsubseteq S'` and
$`E = E'`: the same allocations escaped, in the same order, so the world
names each by the same handle.

*Theorems.* A traced state refines itself, refinement of traced states is
transitive, and entering or leaving a frame keeps refinement.
:::

:::readable Fir.TraceEnd.trace Fir.TraceEnd.trace_after (fingerprint := "565791287545619874")
*Definition: the trace of a way of ending.* A way of ending of the traced
layer, with a result or with UB, shows a trace. After the trace $`t`, it
shows $`t` first.
:::

:::readable Fir.TraceEnd.Allows Fir.TraceEnd.Allows.of_ub Fir.TraceEnd.Allows.after (fingerprint := "10733521865864246037")
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

:::readable Fir.ExtAgree.always Fir.ExtTraceMonotone Fir.ExtTraceMonotone.of_ub (pin := Fir.DialectExtCall) (fingerprint := "13687539404162419082")
*Definition: an external-call rule monotone in the traced layer.* An
_agreement_ of two external calls relates the arguments and the traced
state of each; the one that always holds is the default. In the traced
layer, the external-call rule is monotone at the symbol $`g`, the operand
types $`\vec{t}` and the result types $`\vec{r}`, under an agreement, when,
on arguments $`\vec{v} \sqsubseteq \vec{v}'` of the types $`\vec{t}`, from
traced states $`s \sqsubseteq s'` on which the two calls agree, each way
that $`\mathrm{ext}(g, \vec{v}', \vec{r})` may end from $`s'` is allowed by
a way that $`\mathrm{ext}(g, \vec{v}, \vec{r})` may end from $`s`, by
refinement of its results. The core's external calls agree when both let
escape the same allocations, in the same order. The obligation is asked at
every symbol, since one guarded by its agreement can hold at every symbol.

*Theorem.* An external-call rule that is UB, with the same reason at every
symbol, is monotone under every agreement: UB that shows no act allows every
way of ending.
:::

:::readable Fir.OpTraceMonotone Fir.OpTracePickMonotone Fir.TraceMonotoneOps Fir.Func.TraceOpsMonotone Fir.Func.TraceOpsMonotone.enter Fir.Func.TraceOpsMonotone.jump (fingerprint := "1106816730811437773")
*Definition: an op monotone in the traced layer.* In a semantics in the
traced layer, an op is monotone when, on operands
$`\vec{v} \sqsubseteq \vec{v}'`, what it runs by its own rule on
$`\vec{v}'` refines what it runs on $`\vec{v}`: an op that is not a
terminator, by refinement of its results; a terminator, by going to the
same place. The external-call rule is monotone at a symbol $`g` and the
types $`\vec{t}` of the operands and $`\vec{r}` of the results of a call
when, on arguments $`\vec{v} \sqsubseteq \vec{v}'` of the types
$`\vec{t}`, what it runs on $`\vec{v}'` refines what it runs on
$`\vec{v}`, by refinement of its results. A rule that is UB is monotone,
since UB that shows no act allows every way of ending. The rule of an op
that picks its callee is monotone when, on operands that refine others,
from traced states that refine others, and where the run can call at least
the same symbols, what it picks refines what it picks on those others: UB,
or the same symbol. The ops of a list, or of a function's blocks, are
monotone, under an agreement of external calls (by default the one that
always holds), when each that runs by its own rule, a terminator or an op
with no callee, is; the external-call rule is monotone under the agreement
at the symbol and types of each other op that names a symbol, which goes to
that rule when no function has the symbol; and each op whose callee is
picked has a monotone rule to pick it, and the external-call rule is
monotone under the agreement at every symbol for its operands but the first
and its results.

*Theorems.* A run of such a function starts, and jumps, to the ops of one
of its blocks, all monotone.
:::
