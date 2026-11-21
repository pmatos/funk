import VersoManual
import Fir.Execution.TraceFollow
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a source configuration that follows a target's, which renders
`Fir.Execution.TraceFollow` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "The source follows the target: readable blocks" =>

:::moduleDocs (fingerprint := "18126709599339852174")
:::

:::readable Fir.TCfg.Allows Fir.TCfg.Follows (fingerprint := "5256647327540650826")
*Definition: the source allows a stream.* A source configuration $`c` in
$`M` allows the stream $`T` when it hits UB at some budget after acts refined
by the first acts of $`T`, or shows at every budget some stream $`S` refined
by $`T`.

*Definition: following.* The source configuration $`c` follows the target
configuration $`c'` when both run the same ops of the same function, $`c`'s
environment and traced state are refined by $`c'`'s, and the function and the
ops still to run are monotone in the traced layer where they run by their
own rule.
:::

:::readable Fir.Stream.ShowsRefined.of_prefix Fir.Stream.cat_nil Fir.TShows.congr (fingerprint := "11844157433157971723")
*Theorems.* A trace refined by a prefix of $`l'` is refined by the first acts
of $`l' \cdot T`, for every $`T`. No acts, then $`T`, is $`T`. A run shows a
stream when another with the same paths does.
:::

:::readable Fir.TCfg.Allows.lift Fir.TCfg.exh_iff_traceFrom (fingerprint := "4129631493278157171")
*Theorems.* When every path of every op shows exactly one step, a source that
allows $`T_1` after a move of the marked trace $`t` allows
$`\mathrm{acts}(t') \cdot T_1` before it, when
$`\mathrm{acts}(t) \sqsubseteq \mathrm{acts}(t')`. The paths that run out of
fuel of a callee's entry block, from a traced state with a frame entered, are
those of its traced runs from that traced state.
:::
