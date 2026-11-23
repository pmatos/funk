import VersoManual
import Fir.Execution.TraceCut
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on truncated paths and cuts, which renders
`Fir.Execution.TraceCut` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Truncated paths and cuts: readable blocks" =>

:::moduleDocs (fingerprint := "8210877913279661202")
:::

:::readable Fir.TraceEnd.Truncated Fir.TraceEnd.Cut (fingerprint := "703612785105317921")
*Definition: a cut.* A path $`e` of a run of $`os` with $`n` steps of fuel
is the path with the marked trace $`t` _truncated_ when $`e` runs out of
fuel after $`t_0 \preceq t`, with $`\mathrm{ticks}(t_0) \le n`, and either
$`t_0 = t` or $`n \le W \, \mathrm{ticks}(t_0) + c` for a chain of $`c`
calls that $`os` starts. $`e` is the _cut_ of a path $`e'` of the run with
$`j` more steps when it is the same return, leaving $`j` fewer, if $`e'`
returns and leaves at least $`j`; the same UB; or $`e'` truncated.
:::

:::readable Fir.TraceEnd.Truncated.after Fir.TraceEnd.Truncated.call Fir.TraceEnd.Cut.after_step Fir.TraceEnd.Truncated.picked Fir.TraceEnd.Cut.pickExh (fingerprint := "13331601013469483752")
*Theorems.* A truncated path, after the trace $`t`, is truncated, at a
budget and from ops whose chain bound the fuel that $`t` took. A truncated
path of a callee, its frame left, is a truncated path of the call one step
of fuel later, when the trace is the callee's or the callee spent its fuel
on its steps. A cut after an op of one step, from ops that start no call,
is a cut one step of fuel later. A truncated path of a callee that its op
picked, its frame left, after the acts $`t_0` of the rule that picked it,
is a truncated path of the call two steps of fuel later. A rule that
picks a callee, with no step left for the call, runs out of fuel after
$`t_0`, a cut of one step.
:::

:::readable Fir.TraceEnd.Cut.notStuck (fingerprint := "17920216482317727631")
*Theorem.* A cut is not stuck.
:::
