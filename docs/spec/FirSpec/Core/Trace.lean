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

:::moduleDocs (fingerprint := "15760459583964791149")
:::

:::readable Fir.Core.instDialectTrace Fir.Core.liftsMem Fir.Core.instInhabitedAnswer (fingerprint := "9825455798937681785")
*Definition: the core's traced semantics.* The core shows no event yet, so
its traced semantics is its semantics with memory, lifted onto the memories
of the traced state; it lifts its semantics with memory, and the world has
one answer.
:::

:::readable Fir.Core.trace_args_isRefinedBy Fir.Core.trace_args_isRefinedBy_world (fingerprint := "16027320472332802630")
*Theorems: refined arguments over the core's traced runs.* For every
function $`f` of every core module, wherever a run names the core's
memories, over the spec's traced runs:

$$`\vec{v} \sqsubseteq \vec{v}' \implies \mathrm{observed}(f, \vec{v}) \sqsubseteq \mathrm{observed}(f, \vec{v}')`

calls and recursion included. So at every world, each outcome of $`f` on
$`\vec{v}'` is allowed by an outcome of $`f` on $`\vec{v}`, which shows
the same answers.
:::

:::readable Fir.Core.trace_replaceBody_isRefinedBy_of_from Fir.Core.trace_replaceBody_isRefinedBy_of_from_world (fingerprint := "12259626236440082226")
*Theorems: congruence in a core callee over traced runs.* In a valid core
module $`M`, if $`@g` with the new body $`b`, run in $`M[g := b]` from given
memories, refines $`@g` in $`M`, every function of $`M` is refined over the
spec's traced runs by itself with $`@g`'s new body in $`M[g := b]`, with no
budget, whatever the parameter types of $`@g` and whatever $`b` does to the
memories: every core op has finitely many outcomes. So it is at every
world.
:::
