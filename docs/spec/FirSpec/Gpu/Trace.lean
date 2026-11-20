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

:::moduleDocs (fingerprint := "1163198360710099317")
:::

:::readable Fir.Gpu.coreGpu_instDialectTrace Fir.Gpu.coreGpu_liftsMem Fir.Gpu.coreGpu_instInhabitedAnswer (fingerprint := "5090117320657069958")
*Definition: the sum's traced semantics.* Neither the core nor `gpu` shows
an event yet, so at every work-item the traced semantics of the sum is its
semantics with memory, lifted onto the memories of the traced state; it
lifts its semantics with memory, and the world has one answer.
:::

:::readable Fir.Gpu.trace_args_isRefinedBy Fir.Gpu.trace_args_isRefinedBy_world (fingerprint := "14681190668605144073")
*Theorems: refined arguments over the sum's traced runs.* For every
function of every module of the sum, a module of a nested table included,
wherever a run names the sum's memories, the spec's traced runs on
arguments that refine others refine its traced runs on those others, calls
and recursion included, and so at every world.
:::

:::readable Fir.Gpu.trace_replaceBody_isRefinedBy_of_from Fir.Gpu.trace_replaceBody_isRefinedBy_of_from_world (fingerprint := "1852494778727179770")
*Theorems: congruence in a callee of the sum over traced runs.* For each
table $`t` of a valid module $`M`, if $`@g` of $`t` with the new body $`b`,
run in $`M.\mathrm{nest}(t)[g := b]` from given memories, refines $`@g` in
$`M.\mathrm{nest}(t)`, every function of $`t` is refined over the spec's
traced runs by itself with $`@g`'s new body, with no budget: every op of the
sum has finitely many outcomes. So it is at every world.
:::
