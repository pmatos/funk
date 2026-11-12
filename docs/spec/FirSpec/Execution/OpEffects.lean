import VersoManual
import Fir.Execution.OpEffects
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on effect sets, which renders
`Fir.Execution.OpEffects` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Effect sets: readable blocks" =>

:::moduleDocs (fingerprint := "2807909622879852508")
:::

:::readable Fir.PoisonClass (fingerprint := "2496376182887207449")
*Definition: a poison class.* How an op treats {ref "The-fir-specification--Execution--Poison-and-immediate-UB"}[poison] operands.

```grammar Fir.PoisonClass
\mathit{class}
propagates   \mathsf{propagates}
exception    \mathsf{exception}
```

* $`\mathsf{propagates}`: a poison operand makes every result the op
  returns poison.
* $`\mathsf{exception}`: the op states its own rule for poison operands.
:::

:::readable Fir.MemSet Fir.MemSet.Has (fingerprint := "7194252162724155757")
*Definition: a set of memories.* The memories that an effect touches,
named by the dialect's memory names $`m`:

```grammar Fir.MemSet
\mathit{mems}
these   \{m_1, \dots, m_n\}
every   \top
```

A set of memories $`M` _holds_ $`m` when $`M` lists $`m`, or
$`M = \top`, every memory.
:::

:::readable Fir.Effects (fingerprint := "8832704036850581480")
*Definition: an effect set.* The effects of an op, a set drawn from:

* $`\mathsf{reads}~M`, $`\mathsf{writes}~M` and
  $`\mathsf{allocates}~M`: the op may read, write, or allocate or free in
  the memories of $`M`;
* $`\mathsf{mayUB}`: the op may end in immediate UB;
* $`\mathsf{mayPoison}`: on operands with no poison, a result of the op may
  be poison;
* $`\mathsf{observable}`: the op may add an event to the trace of the run;
* $`\mathsf{control}`: the op is a terminator.

The default is the empty set, $`\emptyset`: reads, writes and allocation
touch no memory, and no other effect is there. An op with the empty set is
_pure_ (ADR-2026-11-09-1541).
:::

:::readable Fir.Effects.all (fingerprint := "8767959454225093829")
*Definition: every effect.* $`\top_{\mathit{eff}}` reads, writes,
allocates and frees in every memory, and has every other effect. It is
what an op declares when nothing narrower is known of it, as of an
external call (ADR-2026-11-09-1541).
:::

:::readable Fir.MemSet.map Fir.Effects.map (fingerprint := "17615428717981311199")
*Definition: renaming memories.* For a map $`f` from one dialect's
memory names to another's, $`f(\{m_1, \dots, m_n\}) = \{f(m_1), \dots,
f(m_n)\}` and $`f(\top) = \top`. An effect set is renamed by renaming the
sets of memories of its reads, writes and allocation, and keeping its
other effects. A dialect's ops are seen so in a larger dialect that holds
its memories among others.
:::

:::readable Fir.DialectEffects (pin := Fir.Effects) (fingerprint := "5406815133426605090")
*Definition: the effect class.* Each dialect names its memories, and gives
each of its ops $`o` a
{ref "The-fir-specification--Execution--Poison-classes"}[poison class],
$`\mathrm{class}(o)`, and a set of effects, $`\mathrm{eff}(o)`, the
effects of the op's own rule. An op with a callee also has its callee's
effects, which $`\mathrm{eff}(o)` leaves out and the effects of an op in
place add ({ref "The-fir-specification--Execution--Function-summaries"}[function summaries]). Every op declares both, so that a dialect
added for new hardware states them too (ADR-2026-10-29-2016,
ADR-2026-11-09-1541).

The poison class says how the op treats poison operands; the effect
$`\mathsf{mayPoison}` says whether a result may be poison when no operand is
(ADR-2026-11-09-1541).
:::
