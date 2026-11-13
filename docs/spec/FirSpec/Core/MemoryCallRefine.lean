import VersoManual
import Fir.Core.MemoryCallRefine
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on congruence in a core callee that
touches no memory, which renders `Fir.Core.MemoryCallRefine`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Congruence in a core callee that touches no memory: readable blocks" =>

:::moduleDocs (fingerprint := "6885859790403288567")
:::

:::readable Fir.Core.Op.effects_touchesNoMemory Fir.Core.summary_touchesNoMemory (pin := Fir.Core.Op.effects) (fingerprint := "17442892947427311925")
*Theorems: no core op declares a memory effect, so core summaries touch no
memory.* The {ref "The-fir-specification--Execution--Effect-sets"}[effects]
of every core op read, write and allocate in no memory. So in a core symbol
table whose functions' calls each name a function of the table, the summary
of every symbol touches no memory.
:::

:::readable Fir.Core.opsIgnoreMemory (pin := Fir.Core.Op.liftsSetM) (fingerprint := "15851737957615372507")
*Theorem: core ops ignore the memories.* At every layout and naming of the
core's memories, each core op that declares no memory effect ignores the
memories: each core op is
{ref "The-fir-specification--Memory--The-core___s-rules-with-memory"}[tied],
so it runs by its rule in the set monad and keeps the memories. An op that
touches memory declares it, so it is not asked.
:::

:::readable Fir.Core.replaceBody_isRefinedBy_of_from (fingerprint := "3364831527639273688")
*Theorem: congruence in a core callee that touches no memory, from given
memories.* Let $`M` be a valid core module, $`g` a function of $`M` with
the symbol $`s` and no pointer parameter, $`b` a region, and
$`M[s \leftarrow b]` the module with $`b` in place of $`g`'s body, in which
the summary of $`s` touches no memory. Take a layout and naming of the
core's memories. If $`g[s \leftarrow b]` in $`M[s \leftarrow b]`, run from
any memories, refines $`g` in $`M`, the memories it ends with included,
then for every function $`f` of $`M`, the runs with memory of
$`f[s \leftarrow b]` in $`M[s \leftarrow b]` refine those of $`f` in $`M`,
calls and recursion included. No budget is asked: the parameter types of
$`g` have finitely many argument vectors, and its new runs do not depend on
the memories.
:::

:::readable Fir.Core.replaceBody_isRefinedBy Fir.Core.caller_isRefinedBy (fingerprint := "15240466193797226971")
*Theorems: congruence in a core callee that touches no memory, with
memory.* With $`M`, $`g`, $`s` and $`b` as above, let the summary of $`s`
touch no memory both in $`M` and in $`M[s \leftarrow b]`. If the runs with
memory of $`g[s \leftarrow b]` in $`M[s \leftarrow b]` refine those of $`g`
in $`M`, then for every function $`f` of $`M`, the runs with memory of
$`f[s \leftarrow b]` in $`M[s \leftarrow b]` refine those of $`f` in $`M`,
calls and recursion included, at every layout and naming of the core's
memories:

$$`\mathrm{runs}^{\mathrm{mem}}_{M,g} \sqsubseteq \mathrm{runs}^{\mathrm{mem}}_{M[s \leftarrow b],g[s \leftarrow b]} \implies \forall f \in M.\ \mathrm{runs}^{\mathrm{mem}}_{M,f} \sqsubseteq \mathrm{runs}^{\mathrm{mem}}_{M[s \leftarrow b],f[s \leftarrow b]}`

So every function of $`M` whose symbol is not $`s`, a caller of $`g` or
not, is refined with memory by itself in $`M[s \leftarrow b]`: the case an
optimizer meets when it rewrites one function. This was stated over the
runs in the set monad until the human's ruling on #373 (2026-11-13); every
core function's summary touches no memory when its module's calls name its
functions, so the form over runs with memory covers each case that one
did. A callee that touches memory, which needs a budget until #214, uses
{ref "The-fir-specification--Memory--Core-functions-with-memory"}[congruence with a bound].

The comparison is between real behaviours when the new function is valid
in the old module's context: then the new module is valid, and neither
module's runs have a stuck path. A body that is stuck at once meets the
hypothesis with an empty behaviour, which refines every source.
:::
