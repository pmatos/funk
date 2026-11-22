import VersoManual
import Fir.Execution.TraceSeen
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on what the world sees, which renders
`Fir.Execution.TraceSeen` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "What the world sees: readable blocks" =>

:::moduleDocs (fingerprint := "15362740429529953075")
:::

:::readable Fir.WUnit.IsRefinedBy Fir.WUnit.isRefinedBy_refl Fir.WUnit.isRefinedBy_trans (fingerprint := "2726711973618413313")
*Definition: units the world sees, refined.* A unit the world sees is
refined by itself, and $`\mathsf{poison}` by any unit:

$$`\mathsf{poison} \sqsubseteq u \qquad u \sqsubseteq u`

Refinement of units the world sees is reflexive and transitive.
:::

:::readable Fir.TraceState.handles Fir.TraceState.worldPtr Fir.TraceState.worldVal Fir.TraceState.worldUnit Fir.TraceState.seen (fingerprint := "15011685363136314882")
*Definition: the world's view.* From the traced state $`s`, where the
memory numbered $`n` is $`\mu(n)`, the world sees the pointer $`p` of the
memory numbered $`n` as:

$$`\mathrm{world}_s(n, p) = \begin{cases} p & p.\mathrm{prov} = \mathsf{none} \\ p[\mathrm{prov} := k] & p.\mathrm{prov} = a,\ (\mu(n), a) \text{ live, at handle } k \text{ of } s.\mathrm{escaped} \\ \mathsf{poison} & \text{otherwise} \end{cases}`

This is how an observer sees a pointer under a renaming, here the renaming
$`\mathrm{handles}(s)` of each escaped allocation to its handle, so a
freed allocation is poison too. A value is seen with each of its pointers
seen so. A unit is seen as its
bits, as $`\mathsf{poison}`, or as the fragment of a pointer seen so, which
is $`\mathsf{poison}` when the pointer is. $`\mathrm{seen}(s)` lists, in the
order of their handles, the units of each escaped allocation that is live,
each seen so, and no units of one that is not.
:::

:::readable Fir.Memory.Memories.freed_eq Fir.TraceState.worldPtr_eq Fir.TraceState.worldVal_isRefinedBy Fir.TraceState.worldUnit_isRefinedBy Fir.TraceState.worldUnits_isRefinedBy Fir.TraceState.seen_isRefinedBy (fingerprint := "8479047628956825252")
*Theorems: refined traced states show refined views.* Memories that refine
each other agree on which allocations are freed. So traced states
$`s \sqsubseteq s'`, which let the same allocations escape in the same
order, see each pointer alike, and:

$$`v \sqsubseteq v' \implies \mathrm{world}_s(v) \sqsubseteq \mathrm{world}_{s'}(v') \qquad \mathrm{seen}(s) \sqsubseteq \mathrm{seen}(s')`

for values, units and lists of units alike.
:::
