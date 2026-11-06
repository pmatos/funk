import VersoManual
import Fir.Core.Rejects
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a rejected function, which renders
`Fir.Core.Rejects` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "A rejected function: readable blocks" =>

:::readable Fir.Core.Rejects.deadBlock (pin := Fir.Core.op) (fingerprint := "15564015379985173766")
*Definition: a function with a block that no branch reaches.* The function
`@f` above, which the theorems below call $`f`, takes no parameters and
returns one $`\mathsf{i32}`. Its entry block `^entry` returns the constant
0, and its second block `^dead` returns the constant 1. Neither block has a
successor, so nothing jumps to `^dead`. Every op uses the location
reference 0.
:::

:::readable Fir.Core.Rejects.deadBlock_reachable (pin := Fir.Core.Rejects.deadBlock) (fingerprint := "15574699308439038797")
*Theorem: only the entry block of the function is reachable.* For every
label $`l`, if $`l` is
{ref "The-fir-specification--Validation--Dominance"}[reachable] in the
function $`f`, then $`l` is the label of `^entry`.

A path starts at the entry, and the function's graph has no edge, so no
path goes further. The next theorem needs it to show that `^dead`
is not reachable.
:::

:::readable Fir.Core.Rejects.deadBlock_rejected (fingerprint := "5009279530636865142")
*Theorem: validation rejects the function, in every module context.* For
every module context $`C`, the function $`f` is not
{ref "The-fir-specification--Validation--The-general-rules"}[valid] in
$`C`.

$$`\forall C.\ \neg\,(C \vdash f~\text{valid})`

A valid function has every block reachable, and `^dead` is not.
Since the rules are propositions, a rejection is a theorem, and this one
shows that the rule of reachability rejects a function that a checker of
types and dominance alone would accept.
:::
