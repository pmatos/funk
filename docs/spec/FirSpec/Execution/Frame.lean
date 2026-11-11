import VersoManual
import Fir.Execution.Frame
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the frame effect, which renders
`Fir.Execution.Frame` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The frame effect: readable blocks" =>

:::moduleDocs (fingerprint := "4886576172366409688")
:::

:::readable Fir.MonadFrame (fingerprint := "9116329985796444310")
*Definition: the frame effect.* A way of computing has the frame effect
when it can run a computation $`x` as the run of one call,
$`\mathrm{frame}(x)`: it enters a frame before $`x` and leaves it after.
The interpreter runs every function in a frame of its own, so that a
call's stack allocations are freed when it returns (ADR-2026-11-09-1548).
:::

:::readable Fir.inFrame Fir.inFrame_setM (pin := Fir.instMonadFrameSetM) (fingerprint := "152058064850931469")
*Definition: a frame of the interpreter.* The interpreter's computations
may also end stuck. Running one in a frame runs, in a frame of the way of
computing, the computation of the ways it may end, stuck ones included.

*Theorem: the set monad has no memory.* In the set monad a frame is the
computation itself: $`\mathrm{frame}(x) = x`. So the runs of the set
monad are those of M0.
:::
