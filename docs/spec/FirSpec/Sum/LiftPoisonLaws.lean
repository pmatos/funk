import VersoManual
import Fir.Sum.LiftPoisonLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a lift's poison obligations, which
renders `Fir.Sum.LiftPoisonLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "A lift's poison obligations: readable blocks" =>

:::moduleDocs (fingerprint := "11697219202051291408")
:::

:::readable Fir.HVector.forall₂_up Fir.HVector.forall₂_down Fir.HVector.map_up (fingerprint := "7072234090836315310")
*Lemmas: relations across an inclusion.* When crossing one value up keeps
a relation, two vectors are related at the types $`a^*` exactly when they
are, crossed up, at $`\iota(a)^*`, and the same crossed down. A computation
over $`A`, moved up, ends with a vector moved up, or with the same UB.
:::

:::readable Fir.TyIncl.Lawful.isPoison_down Fir.HVector.any_down Fir.HVector.all_up Fir.TyIncl.Lawful.poisonOrEq_up Fir.HVector.isRefinedBy_map_up (fingerprint := "17220656936822278559")
*Lemmas: what the obligations look at, across a lawful inclusion.* Across
a lawful inclusion, a value crossed down is poison exactly when it was, a
vector holds poison, or is all poison, exactly when it did, and a value is
poison or equal to another exactly when it was before crossing. So
refinement of what a computation may end with carries over.
:::

:::readable Fir.Dialect.lift.incl_lawful Fir.Dialect.lift.isFilledBy_down (fingerprint := "721175524571914087")
*Lemmas: the lift's values.* $`\hat\iota` is lawful when $`\iota` is. A
vector of the lift
{ref "The-fir-specification--Execution--Poison-classes"}[fills the poison]
of another exactly when it does, moved down to $`e`'s types.
:::

:::readable Fir.Dialect.lift.typesValid_lift Fir.Dialect.lift.propagates_lift (fingerprint := "18352063200702292213")
*Lemmas: valid instances and propagation.* An op whose instance the lift
accepts is one that $`e` accepts over $`d`, when $`e` accepts each type
$`t` of $`d` whose inclusion $`\iota(t)` $`B` accepts. An op of $`e` that
propagates poison over $`d` propagates it in the lift, across a lawful
inclusion.
:::

:::readable Fir.Dialect.lift.lawfulPoison Fir.Dialect.lift.sum_lawfulPoison (fingerprint := "13705583925890202283")
*Theorem: the lift of a lawful extension is lawful.* Let $`B` and $`e`
over $`d` meet the
{ref "The-fir-specification--Execution--Poison-classes"}[poison obligations],
let $`\iota` be lawful, and let $`e` accept each type of $`d` whose
inclusion $`B` accepts. Then the lift over $`B` meets them, and so does
$`B \boxplus e{\uparrow}_\iota`.

Each op of the lift runs by $`e`'s rule on the same values, which only
cross the inclusion, and a lawful inclusion keeps which values are poison
and which refine others. A poison value of a type of $`B` is refined as
$`B` says.
:::
