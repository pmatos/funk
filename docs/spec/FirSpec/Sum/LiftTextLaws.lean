import VersoManual
import Fir.Sum.LiftTextLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the text of a lift, which renders
`Fir.Sum.LiftTextLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The text of a lift: readable blocks" =>

:::moduleDocs (fingerprint := "7214088044110147805")
:::

:::readable Fir.Dialect.lift.lawfulName (fingerprint := "14404641875743537380")
*Theorem: the lift writes its words under its name.* Let $`e` write its
words under its name over $`d`, and let $`d`'s set be in $`B`'s. Then the
lift writes its words under its name over $`B`. Its words are $`e`'s, and
every dialect they name is in $`\mathrm{names}(d) \cdot n_e`, so in
$`\mathrm{names}(B) \cdot n_e`.
:::

:::readable Fir.Dialect.lift.lawfulText (fingerprint := "3480317085186262102")
*Theorem: the text of the lift is lawful.* Let $`B` and $`e` over $`d`
have
{ref "The-fir-specification--Text-format--Grammar"}[lawful text], let
$`B`'s words stay in its set, let $`e` write its words under its name, and
let $`n_e \notin \mathrm{names}(B)`. Then the lift over $`B` has lawful
text.

An op of $`e` is read back from its types included by $`\hat\iota`, which
project back to $`e`'s. A valid type of $`B` names no dialect outside
$`B`'s set, so not $`n_e`, and $`B` reads it back; a valid own type of
$`e` names $`n_e`, and $`e` reads it back.
:::

:::readable Fir.Dialect.lift.sum_lawfulText Fir.Dialect.lift.sum_validIsWellFormed Fir.Dialect.lift.sum_printThenParse (fingerprint := "16665747849072813111")
*Theorems: the round trip over a sum with a lift.* Under the conditions
above, with $`d`'s set in $`B`'s, $`B \boxplus e{\uparrow}_\iota` has
lawful text, every valid module of it is well formed, and
$`\mathrm{parse}(\mathrm{print}(m)) = m` for every well-formed module
$`m`. Each is the theorem for a sum, applied to the lift.
:::
