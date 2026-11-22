import VersoManual
import Fir.Execution.TraceTruncate
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on truncating a traced run, which renders
`Fir.Execution.TraceTruncate` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Truncating a traced run: readable blocks" =>

:::moduleDocs (fingerprint := "13273725330195052366")
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

:::readable Fir.TraceEnd.Truncated.after Fir.TraceEnd.Truncated.call Fir.TraceEnd.Cut.after_step (fingerprint := "17714228740208022935")
*Theorems.* A truncated path, after the trace $`t`, is truncated, at a
budget and from ops whose chain bound the fuel that $`t` took. A truncated
path of a callee, its frame left, is a truncated path of the call one step
of fuel later, when the trace is the callee's or the callee spent its fuel
on its steps. A cut after an op of one step, from ops that start no call,
is a cut one step of fuel later.
:::

:::readable Fir.TraceEnd.Cut.notStuck (fingerprint := "17920216482317727631")
*Theorem.* A cut is not stuck.
:::

:::readable Fir.Func.traceOps_cut (fingerprint := "9151832986990566632")
*Theorem: truncation.* When every path of every op and
of every external call shows exactly one step,
and $`W > 0` exceeds the length of every chain of calls of the module by at
least one, each path of a traced run of ops with $`n + j` steps of fuel
that is not stuck has a cut among the paths of the run with $`n`, from the
same environment and traced state.
:::
