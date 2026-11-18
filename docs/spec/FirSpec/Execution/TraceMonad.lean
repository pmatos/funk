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

:::moduleDocs (fingerprint := "11965682499170283813")
:::

:::readable Fir.Paths Fir.Paths.pure_bind Fir.Paths.bind_pure Fir.Paths.bind_assoc (pin := Fir.Paths.instMonad) (pin := Fir.Paths.instLawfulMonad) (fingerprint := "8066813908157793877")
*Definition: a set of paths.* A computation of $`\mathrm{Paths}` is the set
of the ways it may end, each with a result, and has no UB of its own:
$`\mathrm{pure}(a) = \{a\}` and
$`s \mathbin{>\!\!>\!\!=} f = \{ b \mid \exists a \in s,\ b \in f(a) \}`.

*Theorem: sets of paths are a lawful monad.* `pure` then $`f` is $`f`,
$`s` then `pure` is $`s`, and binds associate.
:::

:::readable Fir.TraceEnd Fir.TraceM Fir.TraceEnd.after Fir.TraceEnd.after_nil Fir.TraceEnd.after_after (fingerprint := "5867186402808184210")
*Definition: the traced layer.* A computation of the traced layer, for acts
$`A` and a state $`\sigma`, maps a state $`S` to the set of the ways it may
end: with a result, the trace $`t` it showed and the state,
$`\mathsf{ok}(x, t, S')`, or with UB, its reason and the trace it showed,
$`\mathsf{error}(r, t)`. A way of ending _after_ the trace $`t` has $`t`
before its own trace. After no trace it is as it was, and after $`t` then
$`t'` it is as after $`t \mathbin{+\!\!+} t'`.
:::

:::readable Fir.TraceM.bind_apply Fir.TraceM.pure_bind Fir.TraceM.bind_pure Fir.TraceM.bind_assoc (pin := Fir.TraceM.instMonad) (pin := Fir.TraceM.instLawfulMonad) (fingerprint := "5157119272785740253")
*Definition: sequences in the traced layer.* $`\mathrm{pure}(x)(S) =
\{\mathsf{ok}(x, [], S)\}`, which shows nothing. A sequence
$`x \mathbin{>\!\!>\!\!=} f` ends, from $`S`, in each way that $`f(a)`
ends from $`S'`, after $`t`, for each $`\mathsf{ok}(a, t, S')` of
$`x(S)`, and in each $`\mathsf{error}(r, t)` of $`x(S)`. A computation never
reads the trace shown before it.

*Theorem: the traced layer is a lawful monad.* `pure` then $`f` is $`f`,
$`x` then `pure` is $`x`, and binds associate, since a trace after two
traces is the trace after their concatenation.
:::

:::readable Fir.MonadEvent (pin := Fir.instMonadUBTraceM) (pin := Fir.instMonadEventTraceMAct) (fingerprint := "15063564997475705100")
*Definition: the event effect.* A way of computing has the event effect
when it can show the event $`e` to the world and go on with the world's
answer, $`\mathrm{emit}(e)`. In the traced layer, every world counts, so an
event may get any answer $`a`, and the computation shows the act:
$`\mathrm{emit}(e)(S) = \{ \mathsf{ok}(a, [\langle e, a\rangle], S) \mid a \}`.
UB shows nothing more and ends the path:
$`\mathrm{ub}~r\,(S) = \{\mathsf{error}(r, [])\}`.
:::

:::readable Fir.TraceM.lift Fir.TraceM.lift_pure Fir.TraceM.lift_bind Fir.MonadMorphism.trace (fingerprint := "13198327729970699913")
*Definition: the lift.* A computation $`x` of the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over the
set monad runs in the traced layer by showing nothing:

$$`\mathrm{lift}(x)(S) = \{ \mathsf{ok}(v, [], S') \mid \mathsf{ok}(v, S') \in x(S) \} \cup \{ \mathsf{error}(r, []) \mid \mathsf{ub}~r \in x(S) \}`

*Theorem: the lift is a monad morphism.* It maps `pure` to `pure`, and a
sequence to the sequence of the lifts, so it maps each computation built
from them, the interpreter's run among them.
:::

:::readable Fir.MonadMorphism.trace_keeps (pin := Fir.instMonadChoiceTraceM) (fingerprint := "9445398385178387790")
*Definition: choice in the traced layer.* A choice of $`w` bits is the lift
of a choice, and so is a choice of a NaN.

*Theorem: the lift keeps choice and UB.* It maps a choice of bits to a
choice of bits, a choice of a NaN to a choice of a NaN, and UB to UB for the
same reason.
:::

:::readable Fir.TraceEnd.mapActs Fir.TraceEnd.mapActs_after Fir.TraceM.mapActs Fir.TraceM.mapActs_pure Fir.TraceM.mapActs_bind Fir.MonadMorphism.mapActs (fingerprint := "4656448102884711578")
*Definition: mapping the acts of traces.* For $`g` that maps each act to a
list of acts, $`\mathrm{map}_g(x)` is $`x` with each trace
$`[a_1, \ldots, a_n]` replaced by $`g(a_1) \mathbin{+\!\!+} \cdots
\mathbin{+\!\!+} g(a_n)`.

*Theorem: mapping acts is a monad morphism.* It maps `pure` to `pure`, and
a sequence to the sequence of the images, since it maps a concatenation of
traces to the concatenation of their images.
:::

:::readable Fir.TraceM.mapActs_mapActs Fir.TraceM.mapActs_singleton Fir.TraceM.mapActs_lift Fir.MonadMorphism.mapActs_keeps (fingerprint := "140070231224752104")
*Theorem: mapping acts twice.* Mapping by $`h` then by $`g` maps each act
$`a` to the image by $`g` of $`h(a)`, and mapping each act to itself
changes nothing.

*Theorem: mapping acts keeps choice and UB.* A lift shows nothing, so its
image is itself. A choice, of bits or of a NaN, is a lift, and UB shows
nothing either, so their images are themselves.
:::

:::readable Fir.MonadMorphism.trace_mapsFrame Fir.MonadMorphism.mapActs_mapsFrame (pin := Fir.instMonadFrameTraceMMemories) (fingerprint := "2848511684395890237")
*Definition: frames in the traced layer.* A frame enters a call before its
computation and leaves it after, as in the state layer, and shows what the
computation shows.

*Theorem: the lift and mapping acts keep frames.* The image of a
computation run as a call's frame is its image run as a call's frame. So,
by the
{ref "The-fir-specification--Execution--Monad-morphisms"}[interpreter's morphism theorem],
each maps the interpreter's run of a dialect to its run by the images of
the dialect's rules.
:::
