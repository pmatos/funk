import VersoManual
import Fir.Execution.TraceAhead
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on more fuel in the traced layer, which
renders `Fir.Execution.TraceAhead` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "More fuel, in the traced layer: readable blocks" =>

:::moduleDocs (fingerprint := "6360229458711917981")
:::

:::readable Fir.TraceEnd.Done Fir.TraceEnd.addLeft Fir.TraceEnd.Done.notStuck Fir.TraceEnd.Done.of_after Fir.TraceEnd.Done.addLeft Fir.TraceEnd.addLeft_zero Fir.TraceEnd.addLeft_after Fir.TraceEnd.addLeft_exit Fir.TraceEnd.Done.of_exit (fingerprint := "7950786738979011767")
*Definitions: done, and more steps left.* A way of ending of a traced run
of ops is _done_ when it is a return or UB; running out of fuel and being
stuck are not. $`e + j` is $`e` with $`j` more steps left when it is a
return, and $`e` otherwise.

*Theorems.* A way of ending that is done is not stuck, and is done before
a trace when it is after it; more steps left keep it done. No more steps
left leave a way of ending as it is. Adding steps left commutes with a
trace before and with leaving a frame, and a way of ending done once a
frame is left is done in it.
:::

:::readable Fir.Func.traceOps_up Fir.Func.traceCall_up (fingerprint := "4430711345801820165")
*Theorem: more fuel keeps a return and UB.* In every traced layer, from the
same environment and traced state, each path $`e` of a run of ops at the
budget $`n` that is done is the path $`e + j` of the run at $`n + j`: a
return with the same values, acts and traced state, leaving $`j` more
steps, or UB after the same acts. So it is of a callee's ops in a call's
frame.
:::
