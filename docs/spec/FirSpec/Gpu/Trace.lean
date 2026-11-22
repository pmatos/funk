import VersoManual
import Fir.Gpu.Trace
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the traced runs of the core and `gpu`, which renders
`Fir.Gpu.Trace` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The traced runs of the core and gpu: readable blocks" =>

:::moduleDocs (fingerprint := "10769285702214994558")
:::

:::readable Fir.Gpu.gpu_instDialectTrace Fir.Gpu.gpu_liftsMem Fir.Gpu.coreGpu_instDialectTrace Fir.Gpu.coreGpu_liftsMem Fir.Gpu.coreGpu_instInhabitedAnswer Fir.Gpu.event_isRefinedBy_trans (fingerprint := "6560627094160518420")
*Definition: the sum's traced semantics.* `gpu` shows no event, so its
traced semantics over the core is its semantics with memory, lifted onto
the memories of the traced state. At every work-item the traced semantics
of the sum is the sum of the core's and `gpu`'s: it shows the core's
events, the external calls, with the core's default answer, and each op
runs by its side's rule, which lifts its rule with memory, so the sum's
traced semantics lifts its semantics with memory. Refinement of its events
is transitive.
:::

:::readable Fir.Gpu.trace_args_isRefinedBy Fir.Gpu.trace_args_isRefinedBy_world (fingerprint := "14681190668605144073")
*Theorems: refined arguments over the sum's traced runs.* For every
function of every module of the sum, a module of a nested table included,
wherever a run names the sum's memories, the spec's traced runs on
arguments that refine others refine its traced runs on those others, calls
and recursion included, divergence too, and so at every world. The traced
layer's own theorem for a dialect that shows events proves it, with no
hypothesis.
:::

:::readable Fir.Gpu.trace_replaceBody_isRefinedBy_of_from Fir.Gpu.trace_replaceBody_isRefinedBy_of_from_world (fingerprint := "1852494778727179770")
*Theorems: congruence in a callee of the sum over traced runs.* For each
table $`t` of a valid module $`M`, if $`@g` of $`t` with the new body $`b`,
run in $`M.\mathrm{nest}(t)[g := b]` from given memories, refines $`@g` in
$`M.\mathrm{nest}(t)`, every function of $`t` is refined over the spec's
traced runs by itself with $`@g`'s new body, with no budget: every op of the
sum has finitely many outcomes. The traced layer's own theorem for a dialect
that shows events proves it, the hypothesis from given memories taken to
the traced one by the lift. So it is at every world.
:::

:::readable Fir.Gpu.traceOpsMonotone Fir.Gpu.opsTraceFinite (fingerprint := "7865552718645386286")
*Theorem: the sum meets the traced obligation.* Every function of the sum
has its ops that run by their own rule monotone in the sum's traced
semantics, wherever a run names the sum's memories: each lifts its rule
with memory and is monotone with memory, and the lift onto the traced
state keeps it.

*Theorem: the sum meets the hypothesis of divergence.* Every op of the sum
that runs by its own rule has finitely many outcomes in its traced
semantics, given the world's answers.
:::
