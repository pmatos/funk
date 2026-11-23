import VersoManual
import Fir.Execution.TraceMoveCases
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on how the paths of a configuration's run go on by its moves, which renders
`Fir.Execution.TraceMoveCases` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "How a run goes on by moves: readable blocks" =>

:::moduleDocs (fingerprint := "7337121668273427082")
:::

:::readable Fir.TCfg.Calls Fir.TCfg.after Fir.TCfg.Calls.enter (fingerprint := "1220242522969492179")
*Definitions: a call.* The first op of a configuration calls $`g` of $`M`,
after the marked trace $`t_0` and $`\delta` steps of fuel, when it names
$`g`, with $`t_0` empty and $`\delta = 0`, or its rule picks $`g` after
$`t_0`, with $`\delta = 1` (#235), and $`g` enters at the ops $`b` with the
environment $`\rho_g` on the call's arguments. After the call returns $`\vec{w}` in the
traced state $`s_1`, the configuration binds the results and goes on with
the rest of its ops.

*Theorem.* A configuration whose first op calls a function enters it by a
move of $`\delta + 1` steps of fuel after $`t_0`.
:::

:::readable Fir.TCfg.exh_succ (fingerprint := "15586140000371697550")
*Theorem: the paths at a budget of one more.* A path of a configuration's
run that runs out of fuel at the budget $`n + 1` goes on by a move of $`F`
steps of fuel, $`F \le 2`, and runs out of fuel at $`n + 1 - F`; or the
first op calls a function $`g`, after $`t_0` and $`\delta \le n` steps,
$`g` returns at $`n - \delta`, the rest runs out of fuel at the steps it
leaves, and the configuration goes on by the move of that return at every
budget at which $`g` returns the same; or $`n = 0`, and the rule that picks
a callee leaves no step for the call.
:::
