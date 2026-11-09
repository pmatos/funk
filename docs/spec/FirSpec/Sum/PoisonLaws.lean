import VersoManual
import Fir.Sum.PoisonLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a sum's poison obligations, which
renders `Fir.Sum.PoisonLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "A sum's poison obligations: readable blocks" =>

:::moduleDocs (fingerprint := "5911828060153534460")
:::

:::readable Fir.HVector.ofSum_toSum Fir.HVector.toSum_ofSum Fir.HVector.forall₂_ofSum Fir.HVector.any_ofSum Fir.HVector.all_toSum (fingerprint := "2660157476304062812")
*Lemmas: moving values keeps them.* $`\downarrow\uparrow v^* = v^*` and
$`\uparrow\downarrow v^* = v^*`. Moving a vector between the base's types
and the sum's keeps, position by position, any relation that is the same
on both, which values are poison, and whether all are.
:::

:::readable Fir.Dialect.sum.map_toSum Fir.Dialect.sum.isFilledBy_ofSum Fir.Dialect.sum.forall₂_refines_ofSum Fir.Dialect.sum.isRefinedBy_map_toSum (fingerprint := "7381981224446135851")
*Lemmas: what the obligations look at, moved.* A computation of the base,
moved to the sum's types, ends with a vector moved up, or with the same
UB. A vector
{ref "The-fir-specification--Execution--Poison-classes"}[fills the poison]
of another, and refines another, at the base's types exactly when it does
at the sum's. So refinement of what a base op may end with carries over to
the sum.
:::

:::readable Fir.Dialect.sum.isRefinedBy_refl Fir.Dialect.sum.isRefinedBy_trans (fingerprint := "11919749328515497936")
*Lemmas: refinement of summed values.* The values of the sum's types refine
themselves, and refine transitively, when each side's do. The refinement
theorems for calls ask both of a dialect's values.
:::

:::readable Fir.Dialect.sum.typesValid_inl Fir.Dialect.sum.typesValid_inr (fingerprint := "3072310842512042320")
*Lemmas: valid instances of each side.* A base op whose instance the sum
accepts is one that the base accepts. An op of $`e` whose instance the
sum accepts is one that $`e` over the base accepts, when $`e` accepts
every type that the base accepts.
:::

:::readable Fir.Dialect.sum.propagates_inl Fir.Dialect.sum.lawfulPoison (fingerprint := "15270034553110167327")
*Theorem: the sum of lawful dialects is lawful.* Let the base and $`e`
over the base meet the
{ref "The-fir-specification--Execution--Poison-classes"}[poison obligations],
and let $`e` accept every type that the base accepts. Then
$`b \boxplus e` meets them.

Each op meets them as an op of its own side. A base op runs by the base's
rule on the same values, seen at the base's types, so a base op that
propagates poison propagates it in the sum, and its totality, its result
on defined operands and its monotonicity carry over. An op of $`e` runs by
$`e`'s rule unchanged.
:::
