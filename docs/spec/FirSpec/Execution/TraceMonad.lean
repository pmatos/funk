import VersoManual
import Fir.Execution.TraceMonad
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the traced layer, which renders
`Fir.Execution.TraceMonad` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The traced layer: readable blocks" =>

:::moduleDocs (fingerprint := "5408976416228713317")
:::

:::readable Fir.Paths Fir.Paths.pure_bind Fir.Paths.bind_pure Fir.Paths.bind_assoc (pin := Fir.Paths.instMonad) (pin := Fir.Paths.instLawfulMonad) (fingerprint := "8066813908157793877")
*Definition: a set of paths.* A computation of $`\mathrm{Paths}` is the set
of the ways it may end, each with a result, and has no UB of its own:
$`\mathrm{pure}(a) = \{a\}` and
$`s \mathbin{>\!\!>\!\!=} f = \{ b \mid \exists a \in s,\ b \in f(a) \}`.

*Theorem: sets of paths are a lawful monad.* `pure` then $`f` is $`f`,
$`s` then `pure` is $`s`, and binds associate.
:::

:::readable Fir.TraceM Fir.MonadEvent (fingerprint := "11584464999158307776")
*Definition: the traced layer.* A computation of the traced layer, for acts
$`A` and a state $`\sigma`, starts from the trace $`t` shown so far and the
state $`S`, and each of its paths ends with a result, the trace and the
state, $`\mathsf{ok}(x, (t', S'))`, or with UB, its reason and the trace,
$`\mathsf{error}(r, t')`. It is Lean's state and exception transformers
over sets of paths.

*Definition: the event effect.* A way of computing has the event effect
when it can show the event $`e` to the world and go on with the world's
answer, $`\mathrm{emit}(e)`.
:::

:::readable Fir.TraceM.lift Fir.TraceM.lift_pure Fir.TraceM.lift_bind Fir.MonadMorphism.trace (fingerprint := "16250081119590119012")
*Definition: the lift.* A computation $`x` of the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over the
set monad runs in the traced layer by keeping the trace:

$$`\mathrm{lift}(x)(t, S) = \{ \mathsf{ok}(v, (t, S')) \mid \mathsf{ok}(v, S') \in x(S) \} \cup \{ \mathsf{error}(r, t) \mid \mathsf{ub}~r \in x(S) \}`

*Theorem: the lift is a monad morphism.* It maps `pure` to `pure`, and a
sequence to the sequence of the lifts, so it maps each computation built
from them, the interpreter's run among them.
:::

:::readable Fir.MonadMorphism.trace_keeps (pin := Fir.instMonadUBTraceM) (pin := Fir.instMonadChoiceTraceM) (pin := Fir.instMonadEventTraceMAct) (fingerprint := "17215997158895057901")
*Definition: choice, UB and events in the traced layer.* A choice of
$`w` bits is the lift of a choice. UB ends the path after the trace shown
so far: $`\mathrm{ub}~r\,(t, S) = \{\mathsf{error}(r, t)\}`. Showing the
event $`e` may get any answer $`a`, since every world counts, and adds the
act to the trace:

$$`\mathrm{emit}(e)(t, S) = \{ \mathsf{ok}(a, (t \mathbin{+\!\!+} [\langle e, a\rangle], S)) \mid a \}`

*Theorem: the lift keeps choice and UB.* It maps a choice of bits to a
choice of bits, and UB to UB for the same reason, after the trace.
:::

:::readable Fir.MonadMorphism.trace_mapsFrame (pin := Fir.instMonadFrameTraceMMemories) (fingerprint := "9351537021001697840")
*Definition: frames in the traced layer.* A frame enters a call before its
computation and leaves it after, as in the state layer, and keeps the
trace.

*Theorem: the lift keeps frames.* Lifting a computation run as a call's
frame is running its lift as a call's frame. So, by the
{ref "The-fir-specification--Execution--Monad-morphisms"}[interpreter's morphism theorem],
the run in the traced layer of a dialect whose semantics there is its
semantics with memory, lifted, is its run with memory, lifted.
:::
