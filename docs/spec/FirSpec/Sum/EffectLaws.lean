import VersoManual
import Fir.Sum.EffectLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a sum's effect obligations, which
renders `Fir.Sum.EffectLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "A sum's effect obligations: readable blocks" =>

:::moduleDocs (fingerprint := "2690883195814480384")
:::

:::readable Fir.HVector.any_toSum (fingerprint := "8356120504750222703")
*Lemma: moving values up keeps poison.* A vector holds poison at the sum's
types, $`\uparrow v^*`, exactly when $`v^*` does at the base's.
:::

:::readable Fir.Dialect.sum.neverUB_inl Fir.Dialect.sum.makesNoPoison_inl Fir.Dialect.sum.liftsSetM (fingerprint := "14214142245583905496")
*Lemmas: a base op keeps its effects in the sum.* A base op that
{ref "The-fir-specification--Execution--Effect-obligations"}[never ends in UB]
in the base never does in the sum, and one that makes no poison in the
base makes none in the sum, wherever a run names the sum's memories by
$`\rho`: it runs by the base's rule with memory at
$`\rho \circ \mathrm{ofBase}`, on the same values, moved down and up,
which keeps which of them are poison, and mapping its results changes no
memory and adds no UB.

*Theorem: a sum of dialects that lift the set monad lifts it.* When the
semantics with memory of the base and of $`e` lift their semantics in the
set monad, so does the sum's: each side's op runs by its rule in the set
monad, with its results mapped, and keeps the memories.
:::

:::readable Fir.Dialect.sum.instDialectMemDenote Fir.Dialect.sum.ownRuleHas_inl Fir.Dialect.sum.ownRuleHas_inr (fingerprint := "17118347255317226753")
*Definition: a sum's semantics with memory.* Where a run names the sum's
memories by $`\rho`, an op of $`e` runs by $`e`'s
{ref "The-fir-specification--Memory--Memory-obligations"}[semantics with memory]
at $`\rho`, and a base op by the base's at
$`\rho \circ \mathrm{ofBase}`: the run names each memory of the base as
the sum does.

*Lemma: a side's op keeps what it has.* What an op of $`e` runs by its own
rule in the sum is what it runs in $`e`. What a base op runs by its own
rule in the sum has every property that it has in the base at
$`\rho \circ \mathrm{ofBase}` and that mapping the results keeps.
:::

:::readable Fir.Dialect.sum.lawfulEffects (fingerprint := "3277287028581617465")
*Theorem: the sum of dialects lawful in their effects is lawful in its
effects.* Let the base and $`e` over the base be
{ref "The-fir-specification--Execution--Effect-obligations"}[lawful in their effects],
and let $`e` accept every type that the base accepts. Then
$`b \boxplus e` is lawful in its effects.

Each op of the sum has its own side's effects, so it meets the
obligations as an op of its own side: a base op by the lemmas above, and an
op of $`e` unchanged. An op is a terminator in the sum exactly when it is
on its side. A base op meets the memory obligations at $`\rho` because it
meets them in the base at $`\rho \circ \mathrm{ofBase}`: renaming its
declaration by $`\mathrm{ofBase}` and then by $`\rho` renames it by
$`\rho \circ \mathrm{ofBase}`, and the obligations hold of the results
mapped up to the sum's types.
:::
