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

:::moduleDocs (fingerprint := "209645641429570924")
:::

:::readable Fir.HVector.any_toSum (fingerprint := "8356120504750222703")
*Lemma: moving values up keeps poison.* A vector holds poison at the sum's
types, $`\uparrow v^*`, exactly when $`v^*` does at the base's.
:::

:::readable Fir.Dialect.sum.neverUB_inl Fir.Dialect.sum.makesNoPoison_inl (fingerprint := "18146934385481034571")
*Lemmas: a base op keeps its effects in the sum.* A base op that
{ref "The-fir-specification--Execution--Effect-obligations"}[never ends in UB]
in the base never does in the sum, and one that makes no poison in the
base makes none in the sum. It runs by the base's rule on the same values,
moved down and up, which keeps which of them are poison, and it ends in UB
in the sum exactly when it does in the base.
:::

:::readable Fir.Dialect.sum.lawfulEffects (fingerprint := "13826328052956240568")
*Theorem: the sum of dialects lawful in their effects is lawful in its
effects.* Let the base and $`e` over the base be
{ref "The-fir-specification--Execution--Effect-obligations"}[lawful in their effects],
and let $`e` accept every type that the base accepts. Then
$`b \boxplus e` is lawful in its effects.

Each op of the sum has its own side's effects, so it meets the
obligations as an op of its own side: a base op by the lemmas above, and an
op of $`e` unchanged. An op is a terminator in the sum exactly when it is
on its side.
:::
