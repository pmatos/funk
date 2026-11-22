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

:::moduleDocs (fingerprint := "14740285995544832933")
:::

:::readable Fir.TCfg.Calls Fir.TCfg.after Fir.TCfg.Calls.enter (fingerprint := "2087880231232390736")
*Definitions: a call.* The first op of a configuration calls $`g` of $`M`
when it names $`g`, and $`g` enters at the ops $`b` with the environment
$`\rho_g` on the call's arguments. After the call returns $`\vec{w}` in the
traced state $`s_1`, the configuration binds the results and goes on with
the rest of its ops.

*Theorem.* A configuration whose first op calls a function enters it by a
move.
:::

:::readable Fir.TCfg.exh_succ Fir.TCfg.exh_succ_of_calls (fingerprint := "8058168867205142269")
*Theorems: the paths at a budget of one more.* A path of a configuration's run
that runs out of fuel at the budget $`n + 1` goes on by a move of one step of
fuel and runs out of fuel at $`n`, or the first op calls a function. When it
calls $`g`, the path is a path of $`g`'s ops in its frame that runs out of
fuel at $`n`, from the traced state with a frame entered; or $`g` returns,
the rest runs out of fuel at the steps it leaves, and the configuration goes
on by the move of that return at every budget at which $`g` returns the
same.
:::

:::readable Fir.List.exists_often_of_mem Fir.TCfg.moves_one_finite (fingerprint := "9354392598166817724")
*Theorems: finitely many moves of one step.* When each of infinitely many
numbers is related to some element of a list, one element is related to
infinitely many of them. When every op that runs by its own rule, and every external call,
has finitely many outcomes, given the world's answers, a configuration has
finitely many moves of one step of fuel whose acts agree with an answer
stream: its first op's outcomes, or the external call's, and the one callee
it may enter.
:::
