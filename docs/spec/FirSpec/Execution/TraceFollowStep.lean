import VersoManual
import Fir.Execution.TraceFollowStep
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on how a source configuration follows one move of the target, which renders
`Fir.Execution.TraceFollowStep` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "One move of the source: readable blocks" =>

:::moduleDocs (fingerprint := "15728244863169221116")
:::

:::readable Fir.TCfg.Follows.step (fingerprint := "15728244863169221116")
*Theorem: the source follows a move.* Let every path of every op and
of every external call show exactly
one step, the target $`M'` run each call as the source $`M` does, by the same
function or a traced black box, and the ops of $`M`'s functions that run by
their own rule be monotone. Let the source configuration $`c` follow the
target's $`c'`, which goes on by a move of the marked trace $`t'` to a
configuration that shows the closed stream $`T_1` at every budget. Then $`c`
allows $`\mathrm{acts}(t') \cdot T_1`, or goes on by a move of its own, of a
marked trace $`t` with $`\mathrm{acts}(t) \sqsubseteq \mathrm{acts}(t')`, to a
configuration that follows the target's.

By the target's move: an op by its own rule, or a call to a declaration by
the external-call rule, is matched by the same op, by monotonicity, or
allowed by UB; a jump by the same jump; entering a callee
named by the same function in both by entering it; its return by the
source's return, allowed at some budget. When the callee is a traced black
box, the source cannot enter the same body. A return of the target's callee
is then matched by the source's own return or UB, by the black box. When the
target enters a black box's callee and goes on inside it, the stream it shows
there is shown by the callee's traced runs, which diverge. The black box
then gives the source's callee UB after a refined prefix, or a divergence
that the target's refines, and the source allows the stream.
:::
