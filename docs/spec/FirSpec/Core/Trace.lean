import VersoManual
import Fir.Core.Trace
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core's traced runs, which renders
`Fir.Core.Trace` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The core's traced runs: readable blocks" =>

:::moduleDocs (fingerprint := "6535809247946832645")
:::

:::readable Fir.Core.instDialectTrace Fir.Core.liftsMem Fir.Core.instInhabitedAnswer (fingerprint := "13717638021267847626")
*Definition: the core's traced semantics.* The core's events are its
external calls, which the world answers with a reply and its actions on
escaped memory; the default answer has no results and no actions. Each op
runs, exits and picks its callee by its rules with memory, lifted onto the
memories of the traced state, and shows no event: an external call is not an op's rule. The
core's external-call rule is, for now, its rule with memory, UB, lifted
too, so the core's traced semantics lifts its semantics with memory; the
next stage of #239 gives an external call its event and the world's
answer.
:::

:::readable Fir.Core.trace_args_isRefinedBy Fir.Core.trace_args_isRefinedBy_world (fingerprint := "16027320472332802630")
*Theorems: refined arguments over the core's traced runs.* For every
function $`f` of every core module, wherever a run names the core's
memories, over the spec's traced runs:

$$`\vec{v} \sqsubseteq \vec{v}' \implies \mathrm{observed}(f, \vec{v}) \sqsubseteq \mathrm{observed}(f, \vec{v}')`

calls and recursion included, divergence too. The traced layer's own
theorem for a dialect that shows events proves it, with no hypothesis: the
core's ops are monotone in the traced layer and have finitely many
outcomes given the world's answers. So at every world, each outcome of $`f` on
$`\vec{v}'` is allowed by an outcome of $`f` on $`\vec{v}`, which shows
the same answers.
:::

:::readable Fir.Core.trace_replaceBody_isRefinedBy_of_from Fir.Core.trace_replaceBody_isRefinedBy_of_from_world (fingerprint := "12259626236440082226")
*Theorems: congruence in a core callee over traced runs.* In a valid core
module $`M`, if $`@g` with the new body $`b`, run in $`M[g := b]` from given
memories, refines $`@g` in $`M`, every function of $`M` is refined over the
spec's traced runs by itself with $`@g`'s new body in $`M[g := b]`, with no
budget, whatever the parameter types of $`@g` and whatever $`b` does to the
memories: every core op has finitely many outcomes. The traced layer's own
theorem for a dialect that shows events proves it: the core's traced
semantics lifts its semantics with memory, so the hypothesis from given
memories gives the traced one from every traced state. So it is at every
world.
:::

:::readable Fir.Core.opLiftsMem Fir.Core.traceOpsMonotone Fir.Core.opsTraceFinite (fingerprint := "14056248587155485240")
*Theorem: each core op lifts its rule.* In the core's traced semantics,
each core op runs by its rule with memory, lifted onto the memories of the
traced state, by definition.

*Theorem: the core meets the traced obligation.* Every core function's
ops that run by their own rule are monotone in the core's traced
semantics, wherever a run names the core's memories: each lifts its rule
with memory and is monotone with memory, and the lift onto the traced
state keeps it. Its external-call rule, UB, is monotone.

*Theorem: the core meets the hypothesis of divergence.* Every core op
that runs by its own rule has finitely many outcomes in the core's traced
semantics, given the world's answers: it has finitely many with memory,
and the lift keeps it. An external call has one, UB.
:::
