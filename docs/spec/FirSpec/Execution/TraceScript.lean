import VersoManual
import Fir.Execution.TraceScript
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on scripted worlds, which renders
`Fir.Execution.TraceScript` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Scripted worlds: readable blocks" =>

:::moduleDocs (fingerprint := "1070449704553100243")
:::

:::readable Fir.WorldScript Fir.WorldScript.world (fingerprint := "6187795664184713745")
*Definition: a scripted world.* A script is a list $`[a_0, \ldots, a_{m-1}]`
of answers, the answer to each event in the order the run shows them. The
world it gives answers the event shown after the acts $`t` with the answer
at place $`|t|`, and with the default answer once $`|t| \ge m`:

$$`w_{\vec{a}}(t, e) = \begin{cases} a_{|t|} & \text{if } |t| < m \\ \mathit{default} & \text{otherwise} \end{cases}`

The answer to an event that hands control outside the program holds the
world's actions on escaped memory too, its writes into escaped
allocations and the heap allocations it creates and frees, so a script
gives them in order with its answers.
:::

:::readable Fir.TOutcome.Follows Fir.TOutcome.trace? (fingerprint := "5746875925175018701")
*Definition: an outcome follows a script.* The trace of a finite outcome,
a return, UB or silent divergence after the trace $`t`, is $`t`; an
outcome that shows acts forever has none. A finite outcome with the trace
$`t = [(e_0, a_0), \ldots, (e_{n-1}, a_{n-1})]` follows the script
$`\vec{b}` when its answers are the script, in order:
$`[a_0, \ldots, a_{n-1}] = \vec{b}`. An outcome that shows acts forever
follows no script.
:::

:::readable Fir.TOutcome.follows_iff (pin := Fir.TOutcome.InWorld) (fingerprint := "10695579304771037489")
*Theorem: following a script is being shown at its world with as many acts
as it has answers.* For every script $`\vec{b}` with $`m` answers and
every outcome with the finite trace $`t`, the outcome follows $`\vec{b}`
exactly when it is shown at the world $`w_{\vec{b}}` and $`|t| = m`. So a
script that answers fewer events than a run shows, or more, fits none of
its outcomes, as a choice sequence that is too short or too long fits no
path of a run.
:::
