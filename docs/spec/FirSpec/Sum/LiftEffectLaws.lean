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

:::moduleDocs (fingerprint := "14690532284854476308")
:::

:::readable Fir.Dialect.lift.instDialectMemDenote Fir.Dialect.lift.ownRuleHas_lift (fingerprint := "7157026062623711188")
*Definition: the lift's semantics with memory.* Where a run names the
lift's memories by $`\rho`, an op of the lift runs by $`e`'s
{ref "The-fir-specification--Memory--Memory-obligations"}[semantics with memory]
at $`\rho \circ \hat\mu`, on its operands moved down across $`\hat\iota`,
with its results moved up.

*Lemma: an op of $`e` keeps what it has.* What an op of the lift runs by
its own rule has every property that it has in $`e` at
$`\rho \circ \hat\mu` and that mapping the results keeps.
:::

:::readable Fir.HVector.any_up (fingerprint := "309306349894809047")
*Lemma: crossing up keeps poison.* Across a lawful inclusion, a vector
crossed up holds poison exactly when it did.
:::

:::readable Fir.Dialect.lift.neverUB_lift Fir.Dialect.lift.makesNoPoison_lift Fir.Dialect.lift.liftsSetM (fingerprint := "15992739990474350256")
*Lemmas: an op of $`e` keeps its effects in the lift.* An op of $`e` that
{ref "The-fir-specification--Execution--Effect-obligations"}[never ends in UB]
over $`d` never does in the lift, wherever a run names the lift's memories
by $`\rho`: it runs by $`e`'s rule with memory at $`\rho \circ \hat\mu`, and
mapping its results adds no UB. One that makes no poison over $`d` makes
none in the lift, across a lawful inclusion, which keeps which values are
poison both ways.

*Theorem: the lift of an extension that lifts the set monad lifts it.*
When $`e`'s semantics with memory over $`d` lifts its semantics in the set
monad, so does the lift's: each op runs by $`e`'s rule in the set monad,
with its values crossing the inclusion, and keeps the memories.
:::

:::readable Fir.Dialect.lift.lawfulEffects Fir.Dialect.lift.sum_lawfulEffects (fingerprint := "3874471640347852484")
*Theorem: the lift of an extension lawful in its effects is lawful in its
effects.* Let $`e` over $`d` be
{ref "The-fir-specification--Execution--Effect-obligations"}[lawful in its effects],
let $`\iota` be lawful, and let $`e` accept each type of $`d` whose
inclusion $`B` accepts. Then the lift over $`B` is lawful in its effects.
When $`B` is lawful in its effects too, so is
$`B \boxplus e{\uparrow}_\iota`, by the theorem on sums.

Each op of the lift has $`e`'s effects and runs by $`e`'s rule on the same
values, which only cross the inclusion; it is a terminator exactly when it
is in $`e`. It meets the memory obligations at $`\rho` because it meets
them in $`e` at $`\rho \circ \hat\mu`, and its declaration renamed by
$`\hat\mu` and then by $`\rho` is its declaration renamed by
$`\rho \circ \hat\mu`.
:::
