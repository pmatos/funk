import VersoManual
import Fir.Execution.TraceWorld
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the world and escaped memory, which
renders `Fir.Execution.TraceWorld` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "The world and escaped memory: readable blocks" =>

:::moduleDocs (fingerprint := "7166734696564331001")
:::

:::readable Fir.TraceState Fir.TraceState.init (fingerprint := "3108308862273180019")
*Definition: the traced state.* The state of a traced run is a pair
$`(S, E)` of its memories $`S` and the list $`E` of the allocations that
escaped to the world, each a pair $`(x, a)` of a memory and an allocation
of it, in the order they escaped. The world names the allocation $`E_k` by
its _handle_ $`k`. A run starts from $`(\varnothing, [])`: the empty
memories, outside every call, and nothing escaped.
:::

:::readable Fir.TraceM.liftMem Fir.TraceM.liftMem_pure Fir.TraceM.liftMem_bind Fir.MonadMorphism.traceMem (fingerprint := "8206400074006116789")
*Definition: the lift onto the memories.* A computation $`x` of the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] runs in
the traced layer on the memories of the traced state, showing nothing and
keeping what escaped:

$$`\mathrm{lift}(x)(S, E) = \{ \mathsf{ok}(v, [], (S', E)) \mid \mathsf{ok}(v, S') \in x(S) \} \cup \{ \mathsf{error}(r, []) \mid \mathsf{ub}~r \in x(S) \}`

*Theorem: the lift is a monad morphism.* It maps `pure` to `pure`, and a
sequence to the sequence of the lifts.
:::

:::readable Fir.TraceM.liftMem_keep Fir.MonadMorphism.traceMem_keeps (fingerprint := "12202616363407195315")
*Theorem: the lift keeps choice and UB.* A computation that keeps the
memories, lifted onto the memories, is that computation lifted onto the
traced state. A choice of bits or of a NaN keeps the memories, so the lift
maps it to the choice of the traced layer, and it maps UB to UB for the
same reason.
:::

:::readable Fir.MonadMorphism.traceMem_mapsFrame Fir.MonadMorphism.mapActs_mapsFrame (pin := Fir.instMonadFrameTraceMTraceState) (fingerprint := "14731802492520594715")
*Definition: frames in the traced layer.* A frame enters a call on the
memories before its computation, and leaves it after, freeing the call's
stack allocations, which may have escaped. What escaped stays escaped, and
the frame shows what its computation shows.

*Theorem: the lift and mapping acts keep frames.* The image of a
computation run as a call's frame is its image run as a call's frame. So,
by the
{ref "The-fir-specification--Execution--Monad-morphisms"}[interpreter's morphism theorem],
each maps the interpreter's run of a dialect to its run by the images of
the dialect's rules.
:::

:::readable Fir.TraceState.escape Fir.TraceM.escape Fir.TraceM.handle (fingerprint := "5306423327752119627")
*Definition: escaping.* The allocation $`(x, a)` escapes from $`(S, E)`
with the handle $`k` when $`E_k = (x, a)`; when it is not in $`E`, it joins
it at the end, with the handle $`|E|`. Only a live allocation escapes: an
id that the memory has not allocated, or a freed allocation, which a
dangling pointer points into, has no handle, and nothing escapes. The effect
$`\mathrm{escape}(x, a)` lets it escape and gives its handle;
$`\mathrm{handle}(k)` gives the allocation $`E_k`, if there is one. An op
that hands an address to code outside the program lets each allocation that
the address, or an allocation that already escaped, reaches escape, in an
order that never depends on allocation ids.
:::

:::readable Fir.WUnit Fir.WorldAct Fir.WUnit.resolve (fingerprint := "11727295630581856659")
*Definition: the world's actions.* The world writes units that are bits,
poison, or the fragment $`i` of a pointer of the memory numbered $`m`, into
the escaped allocation of handle $`h`, if any, at the offset $`o`. An
action of the world is one of:

$$`\mathsf{store}~h~o~\vec{u} \qquad \mathsf{alloc}~m~n~k \qquad \mathsf{free}~h`

a write of the units $`\vec{u}` into the escaped allocation of handle $`h`
from the offset $`o`; a heap allocation of $`n` units aligned to $`2^k`
in the memory numbered $`m`, since every alignment is a power of two; and
the freeing of the escaped allocation of handle $`h`. A unit the world writes becomes a unit of a memory whose units
are $`w` bits wide: its bits taken modulo $`2^w`, or the fragment of a
pointer into $`E_h`, which must belong to the pointer's memory.
:::

:::readable Fir.WorldAct.apply Fir.WorldAct.applyAll Fir.TraceM.ask (fingerprint := "14959616505777134246")
*Definition: the world takes its actions.* On $`(S, E)`, where the memory
numbered $`n` is $`\mu(n)`:

* $`\mathsf{store}~h~o~\vec{u}` stores $`\vec{u}` through the pointer to
  the offset $`o` of $`E_h`, which must not fault: the allocation is live,
  and the units are inside it;
* $`\mathsf{alloc}~m~n~k` allocates $`n` units aligned to $`2^k` on
  the heap of $`\mu(m)`, and the allocation escapes at once;
* $`\mathsf{free}~h` frees $`E_h`, which must be a live heap allocation.

Any other action is one the world cannot take. The world takes a list of
actions in order.

*Definition: an event the world answers with memory.* $`\mathrm{ask}_\mu(e)`
shows the event $`e`, and the world answers with a result $`a` and a list
of actions $`\vec{w}` that it can take:

$$`\mathrm{ask}_\mu(e)(S, E) = \{ \mathsf{ok}(a, [\langle e, (a, \vec{w})\rangle], (S', E')) \mid \vec{w}~\text{takes}~(S, E)~\text{to}~(S', E') \}`

The act holds the result and the actions, so a target answered at the same
world takes the same actions, by handle, as the source.
:::
