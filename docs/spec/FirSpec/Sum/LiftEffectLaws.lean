import VersoManual
import Fir.Sum.LiftEffectLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a lift's effect obligations, which
renders `Fir.Sum.LiftEffectLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "A lift's effect obligations: readable blocks" =>

:::moduleDocs (fingerprint := "5367318829686041040")
:::

:::readable Fir.HVector.any_up (fingerprint := "309306349894809047")
*Lemma: crossing up keeps poison.* Across a lawful inclusion, a vector
crossed up holds poison exactly when it did.
:::

:::readable Fir.Dialect.lift.neverUB_lift Fir.Dialect.lift.makesNoPoison_lift (fingerprint := "2433529917330163221")
*Lemmas: an op of $`e` keeps its effects in the lift.* An op of $`e` that
{ref "The-fir-specification--Execution--Effect-obligations"}[never ends in UB]
over $`d` never does in the lift: it ends in UB in the lift exactly when it
does in $`e`. One that makes no poison over $`d` makes none in the lift,
across a lawful inclusion, which keeps which values are poison both ways.
:::

:::readable Fir.Dialect.lift.lawfulEffects Fir.Dialect.lift.sum_lawfulEffects (fingerprint := "7791440102001755658")
*Theorem: the lift of an extension lawful in its effects is lawful in its
effects.* Let $`e` over $`d` be
{ref "The-fir-specification--Execution--Effect-obligations"}[lawful in its effects],
let $`\iota` be lawful, and let $`e` accept each type of $`d` whose
inclusion $`B` accepts. Then the lift over $`B` is lawful in its effects.
When $`B` is lawful in its effects too, so is
$`B \boxplus e{\uparrow}_\iota`, by the theorem on sums.

Each op of the lift has $`e`'s effects and runs by $`e`'s rule on the same
values, which only cross the inclusion; it is a terminator exactly when it
is in $`e`.
:::
