import VersoManual
import Fir.Core.Event
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core's events, which renders
`Fir.Core.Event` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The core's events: readable blocks" =>

:::moduleDocs (fingerprint := "4338696235512806621")
:::

:::readable Fir.Core.Event Fir.Core.Reply (fingerprint := "12235446563930257723")
*Definition: the core's events.* An event of the core is an external call:

```grammar Fir.Core.Event
\mathit{event}
call   \mathsf{call}~g~\vec{v}~\vec{u}
```

$`\mathsf{call}~g~\vec{v}~\vec{u}` calls the declaration $`g` on the
arguments $`\vec{v}`, as the world sees them, when the world sees the units
$`\vec{u}` of the escaped allocations, by handle. The world answers with a
reply, the call's results with each pointer naming its allocation by its
handle, and its actions on escaped memory.
:::

:::readable Fir.Core.Event.IsRefinedBy Fir.Core.Event.isRefinedBy_refl Fir.Core.Event.isRefinedBy_trans (fingerprint := "9440954353975539700")
*Definition: refinement of events.* An event is refined by an event of the
same symbol whose arguments and units refine its own one by one, poison by
any value:

$$`\mathsf{call}~g~\vec{v}~\vec{u} \sqsubseteq \mathsf{call}~g'~\vec{v}'~\vec{u}' \iff g = g' \wedge \vec{v} \sqsubseteq \vec{v}' \wedge \vec{u} \sqsubseteq \vec{u}'`

It is reflexive and transitive.
:::

:::readable Fir.Core.Event.ofCall Fir.Core.Event.ofCall_isRefinedBy (fingerprint := "9180825267022142938")
*Definition: the event of an external call.* From the traced state $`s`,
once the call has let escape what it reaches, an external call of $`g` on
$`\vec{v}` shows

$$`\mathrm{ofCall}_s(g, \vec{v}) = \mathsf{call}~g~\mathrm{world}_s(\vec{v})~\mathrm{seen}(s)`

*Theorem: refined calls show refined events.* From traced states
$`s \sqsubseteq s'`, on arguments $`\vec{v} \sqsubseteq \vec{v}'`:

$$`\mathrm{ofCall}_s(g, \vec{v}) \sqsubseteq \mathrm{ofCall}_{s'}(g, \vec{v}')`
:::
