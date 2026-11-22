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

:::moduleDocs (fingerprint := "15085586242917980642")
:::

:::readable Fir.Core.Op.effects_touchesNoMemory Fir.Core.Op.touchesMemory_false Fir.Core.reachesNoMemory Fir.Core.reachesNoMemory_of_all (pin := Fir.Core.Op.effects) (fingerprint := "634682361875928498")
*Theorems: a core op declares a memory effect exactly when it touches
memory, and a core function with no allocation, load, store, copy, move,
fill or turn of a pointer into an integer or back in reach reaches no
memory.* The {ref "The-fir-specification--Execution--Effect-sets"}[effects]
of every core op that touches no memory, every one but
$`\mathsf{alloca}`, the loads and stores, the copies and moves, the
fills, $`\mathsf{ptr\_expose}` and $`\mathsf{ptr\_from\_int}`, read,
write and allocate in no memory, and an op that declares no memory effect touches no memory,
since $`\mathsf{alloca}_N` declares that it allocates in memory $`N`,
$`\mathsf{load}_N` of an integer, a pointer or a float that it reads it,
$`\mathsf{store}_N` of any of them that it writes it, and
$`\mathsf{memcpy}_N` and $`\mathsf{memmove}_N` that they read it,
$`\mathsf{memset}_N` that it writes it, and $`\mathsf{ptr\_expose}_N` and
$`\mathsf{ptr\_from\_int}_N` that they read it. So in a core symbol table, the
function named $`s`
{ref "The-fir-specification--Memory--Touching-no-memory"}[reaches no memory]
when no function that the walk from $`s` reaches, $`s`'s own included, has
an op that touches memory; and so it does when no function of the table
has one.
:::

:::readable Fir.Core.opsIgnoreMemory (pin := Fir.Core.Op.liftsSetM) (fingerprint := "4616432161133284535")
*Theorem: core ops ignore the memories.* At every layout and naming of the
core's memories, each core op that declares no memory effect ignores the
memories: such an op touches no memory, so either it reads no item and is
{ref "The-fir-specification--Memory--The-core___s-rules-with-memory"}[tied],
running by its rule in the set monad and keeping the memories, or it is
$`\mathsf{fieldaddr}` or $`\mathsf{globaladdr}`, which read an item, not
memory, and give their results at once and keep them
({ref "The-fir-specification--Memory--Field-address-obligations"}[field address obligations],
{ref "The-fir-specification--Memory--Global-address-obligations"}[global address obligations]).
$`\mathsf{alloca}`, the loads and stores, of an integer, a pointer or a
float, the copies and moves, the fills, $`\mathsf{ptr\_expose}` and
$`\mathsf{ptr\_from\_int}`, which touch memory, declare it, so they are
not asked.
:::

:::readable Fir.Core.opsFinite (pin := Fir.Core.Op.liftsSetM) (pin := Fir.OpsFinite) (fingerprint := "15692013965595329733")
*Theorem: core ops have finitely many outcomes.* At every layout and
naming of the core's memories, each core op that runs by its own rule has
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many outcomes]
with memory. Each core op that touches no memory and reads no item is
{ref "The-fir-specification--Memory--The-core___s-rules-with-memory"}[tied],
so it runs by its rule in the set monad and keeps the memories. Its rule in
the set monad is the set of its rule in the
{ref "The-fir-specification--Memory--The-core-dialect-in-the-tree-of-choices"}[tree of choices],
by the morphism that keeps choice and UB, and a tree's choice of $`w` bits
has $`2^w` options. $`\mathsf{alloca}` has no tie, and has
{ref "The-fir-specification--Memory--Stack-allocation-obligations"}[one outcome]
by its own rule; the loads and stores of an integer, a pointer or a
float have no tie either, and have at most one that ends
({ref "The-fir-specification--Memory--Load-obligations"}[load obligations],
{ref "The-fir-specification--Memory--Store-obligations"}[store obligations]).
$`\mathsf{fieldaddr}` and $`\mathsf{globaladdr}` have no tie, and have
one outcome by their own rules
({ref "The-fir-specification--Memory--Field-address-obligations"}[field address obligations],
{ref "The-fir-specification--Memory--Global-address-obligations"}[global address obligations]).
The copies and moves and the fills have no tie either,
and have at most one that ends for each length, of which a poison length
chooses one of finitely many
({ref "The-fir-specification--Memory--Copy-and-move-obligations"}[copy and move obligations],
{ref "The-fir-specification--Memory--Fill-obligations"}[fill obligations]).
$`\mathsf{ptr\_expose}` and $`\mathsf{ptr\_from\_int}` have no tie, and
have finitely many by their own rules
({ref "The-fir-specification--Memory--Pointers-as-integers-obligations"}[pointers as integers obligations]).
:::

:::readable Fir.Core.replaceBody_isRefinedBy_of_from Fir.Core.caller_isRefinedBy_of_from (fingerprint := "3664423118415088410")
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

:::readable Fir.Core.replaceBody_isRefinedBy Fir.Core.caller_isRefinedBy (fingerprint := "13131969631230233583")
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
reaches no memory when no function in its reach has an
$`\mathsf{alloca}`, a load, a store, a copy, a move or a fill, the core
ops that touch memory. Its hypothesis is refinement with memory, from the
memories a run starts with, which says nothing of a callee that
touches memory; such a callee uses the theorem from given memories above.

Congruence goes through the lawful class, so it asks for a valid module, as
the form over the runs in the set monad did. The comparison is between real behaviours when the new function is valid
in the old module's context: then the new module is valid, and neither
module's runs have a stuck path. A body that is stuck at once meets the
hypothesis with an empty behaviour, which refines every source.
:::
