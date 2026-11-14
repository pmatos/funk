import VersoManual
import Fir.Core.MemoryCallRefine
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on congruence in a core callee, which
renders `Fir.Core.MemoryCallRefine`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Congruence in a core callee: readable blocks" =>

:::moduleDocs (fingerprint := "11776099395834119705")
:::

:::readable Fir.Core.Op.effects_touchesNoMemory Fir.Core.Op.touchesMemory_false Fir.Core.reachesNoMemory Fir.Core.reachesNoMemory_of_all (pin := Fir.Core.Op.effects) (fingerprint := "17722727725292493020")
*Theorems: a core op declares a memory effect exactly when it touches
memory, and a core function with no allocation in reach reaches no
memory.* The {ref "The-fir-specification--Execution--Effect-sets"}[effects]
of every core op that touches no memory, every one but
$`\mathsf{alloca}`, read, write and allocate in no memory, and an op that
declares no memory effect touches no memory, since $`\mathsf{alloca}_N`
declares that it allocates in memory $`N`. So in a core symbol table, the
function named $`s`
{ref "The-fir-specification--Memory--Touching-no-memory"}[reaches no memory]
when no function that the walk from $`s` reaches, $`s`'s own included, has
an op that touches memory; and so it does when no function of the table
has one.
:::

:::readable Fir.Core.opsIgnoreMemory (pin := Fir.Core.Op.liftsSetM) (fingerprint := "8906603344257890118")
*Theorem: core ops ignore the memories.* At every layout and naming of the
core's memories, each core op that declares no memory effect ignores the
memories: such an op touches no memory, so it is
{ref "The-fir-specification--Memory--The-core___s-rules-with-memory"}[tied],
and runs by its rule in the set monad and keeps the memories.
$`\mathsf{alloca}`, which touches memory, declares it, so it is not
asked.
:::

:::readable Fir.Core.opsFinite (pin := Fir.Core.Op.liftsSetM) (pin := Fir.OpsFinite) (fingerprint := "8297816828923716502")
*Theorem: core ops have finitely many outcomes.* At every layout and
naming of the core's memories, each core op that runs by its own rule has
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many outcomes]
with memory. Each core op that touches no memory is
{ref "The-fir-specification--Memory--The-core___s-rules-with-memory"}[tied],
so it runs by its rule in the set monad and keeps the memories. Its rule in
the set monad is the set of its rule in the
{ref "The-fir-specification--Memory--The-core-dialect-in-the-tree-of-choices"}[tree of choices],
by the morphism that keeps choice and UB, and a tree's choice of $`w` bits
has $`2^w` options. $`\mathsf{alloca}` has no tie, and has
{ref "The-fir-specification--Memory--Stack-allocation-obligations"}[one outcome]
by its own rule.
:::

:::readable Fir.Core.replaceBody_isRefinedBy_of_from Fir.Core.caller_isRefinedBy_of_from (fingerprint := "11864989512908111455")
*Theorem: congruence in a core callee, from given memories.* Let $`M` be a
valid core module, $`g` a function of $`M` with the symbol $`s`, $`b` a
region, and $`M[s \leftarrow b]` the module with $`b` in place of $`g`'s
body. Take a layout and naming of the core's memories. If
$`g[s \leftarrow b]` in $`M[s \leftarrow b]`, run from any memories,
refines $`g` in $`M`, the memories it ends with included, then for every
function $`f` of $`M`, the runs with memory of $`f[s \leftarrow b]` in
$`M[s \leftarrow b]` refine those of $`f` in $`M`, calls and recursion
included. No budget is asked, whatever the parameter types of $`g`,
pointers included, and whatever $`b` does to the memories: every core op
has finitely many outcomes, so
{ref "The-fir-specification--Memory--Congruence-in-the-callee-with-ops-of-finitely-many-outcomes"}[congruence with ops of finitely many outcomes]
applies (#214). So every function of $`M` whose symbol is not $`s`, a caller
of $`g` or not, is refined with memory by itself in $`M[s \leftarrow b]`.
:::

:::readable Fir.Core.replaceBody_isRefinedBy Fir.Core.caller_isRefinedBy (fingerprint := "11835033131941382943")
*Theorems: congruence in a core callee that touches no memory, with
memory.* With $`M`, $`g`, $`s` and $`b` as above, let $`s` reach no memory
both in $`M` and in $`M[s \leftarrow b]`. If the runs with
memory of $`g[s \leftarrow b]` in $`M[s \leftarrow b]` refine those of $`g`
in $`M`, then for every function $`f` of $`M`, the runs with memory of
$`f[s \leftarrow b]` in $`M[s \leftarrow b]` refine those of $`f` in $`M`,
calls and recursion included, at every layout and naming of the core's
memories:

$$`\mathrm{runs}^{\mathrm{mem}}_{M,g} \sqsubseteq \mathrm{runs}^{\mathrm{mem}}_{M[s \leftarrow b],g[s \leftarrow b]} \implies \forall f \in M.\ \mathrm{runs}^{\mathrm{mem}}_{M,f} \sqsubseteq \mathrm{runs}^{\mathrm{mem}}_{M[s \leftarrow b],f[s \leftarrow b]}`

So every function of $`M` whose symbol is not $`s`, a caller of $`g` or
not, is refined with memory by itself in $`M[s \leftarrow b]`: the case an
optimizer meets when it rewrites one function. Nothing is asked of the
parameter types of $`g`, pointers included. Since $`g` reaches no memory
in either module, its
{ref "The-fir-specification--Memory--Congruence-in-a-callee-that-touches-no-memory"}[runs from given memories are its runs with memory],
so the hypothesis gives refinement from given memories and the theorem
above applies (#214). Until #214 this form asked that $`g` have no pointer
parameter, as the human ruled on #373 (2026-11-13). A core function
reaches no memory when no function in its reach has an $`\mathsf{alloca}`,
the core op that touches memory. Its hypothesis is refinement
with memory, from the empty memories, which says nothing of a callee that
touches memory; such a callee uses the theorem from given memories above.

Congruence goes through the lawful class, so it asks for a valid module, as
the form over the runs in the set monad did. The comparison is between real behaviours when the new function is valid
in the old module's context: then the new module is valid, and neither
module's runs have a stuck path. A body that is stuck at once meets the
hypothesis with an empty behaviour, which refines every source.
:::
