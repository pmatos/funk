import VersoManual
import Fir.Execution.TracePaths
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on paths of the interpreter in the traced layer, which renders
`Fir.Execution.TracePaths` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Paths of the interpreter in the traced layer: readable blocks" =>

:::moduleDocs (fingerprint := "12585337159390945984")
:::

:::readable Fir.TraceEnd.NotStuck Fir.TraceEnd.NotStuck.of_after Fir.TraceEnd.notStuck_error Fir.TraceEnd.notStuck_ok Fir.TraceEnd.Allows.notStuck (fingerprint := "4952022327716549937")
*Definition: a way of ending that is not stuck.* A way that a computation of
the interpreter ends in the traced layer is not stuck when it is UB or a
value. One that is not stuck after a trace is not stuck before it. A way
of ending that allows another is not stuck when the relation on what they
give relates no stuck path to anything.
:::

:::readable Fir.TraceM.run_except_bind Fir.TraceM.run_except_pure Fir.TraceM.run_liftExcept Fir.TraceM.run_lift (fingerprint := "13754838662293161135")
*Theorems: the interpreter's building blocks.* A sequence $`x \mathbin{>\!\!>\!\!=} f`
of the interpreter ends, from $`s`, in one of three ways: $`x` ends with
the value $`a` after the trace $`t` in $`s'`, and $`f(a)` ends from $`s'`,
after $`t`; or $`x` ends stuck, and so does the sequence, after $`x`'s
trace; or $`x` hits UB, and so does the sequence. `pure` and a check end at
once with what they hold, showing nothing. A computation of the traced
layer that the interpreter runs ends as it does, and is never stuck.
:::

:::readable Fir.TraceM.run_lift_bind Fir.TraceM.run_liftExcept_bind Fir.TraceM.run_stuck (fingerprint := "2254239457126893946")
*Theorems: what follows a lifted computation or a check.* A path of a
lifted computation, then $`g`, goes on by $`g` from one of its results
after its acts, or ends where it hits UB. A path of a check, then $`g`,
that is not stuck goes on from the value the check holds, from the same
traced state; a check that fails has no path that is not stuck.
:::
