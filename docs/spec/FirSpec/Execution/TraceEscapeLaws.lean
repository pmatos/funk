import VersoManual
import Fir.Execution.TraceEscapeLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the closure that an external call
lets escape, which renders `Fir.Execution.TraceEscapeLaws`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "What an external call lets escape is the closure: readable blocks" =>

:::moduleDocs (fingerprint := "9305002155460043735")
:::

:::readable Fir.TraceState.Reaches (fingerprint := "4147047447065825250")
*Definition: reachable allocations.* In the traced state $`s`, from the
pointers $`\vec{q}`:

```grammar Fir.TraceState.Reaches
\mathit{reaches}
escaped   (x, a) \in s.\mathrm{escaped}
arg   (n, p) \in \vec{q},\ p.\mathrm{prov} = a,\ (\mu(n), a)\ \text{live}
unit   (x, a)\ \text{reachable},\ (n, p) \in \mathrm{ptrs}_s(x, a),\ p.\mathrm{prov} = b,\ (\mu(n), b)\ \text{live}
```

an allocation is reachable when it had escaped, when it is the live
allocation of one of the pointers, or when it is the live allocation of a
pointer that a unit of a reachable allocation holds.
:::

:::readable Fir.TraceState.live_congr Fir.TraceState.ptrsIn_congr Fir.TraceState.mem_escape Fir.TraceState.mem_escapePtrs Fir.TraceState.escapePtrs_sound Fir.TraceState.reach_sound (fingerprint := "5591810211785430723")
*Lemmas: the steps of the walk.* Traced states with the same memories
agree on which allocations are live and on the pointers each holds. A live
allocation has a handle once it escapes, so after pointers' allocations
escape, each of their live allocations has one. Letting pointers'
allocations escape adds only their live allocations, and the walk adds
only the live allocations that pointers in escaped allocations point into.
:::

:::readable Fir.TraceState.escapeCall_sound (fingerprint := "10269368574661714853")
*Theorem: an external call lets escape only what it reaches.* Every
allocation in $`\mathrm{escapeCall}_s(\vec{q}).\mathrm{escaped}` is
reachable from $`\vec{q}` in $`s`.
:::

:::readable Fir.TraceState.Covered Fir.TraceState.reach_covered (fingerprint := "16913563874998235415")
*Lemma: the walk covers the escaped list.* The escaped allocations below
the handle $`k` are covered when the live allocation of every pointer that
one of their units holds has a handle. A walk from a handle below which
the escaped allocations are covered ends with all of them covered.
:::

:::readable Fir.TraceState.escapeCall_closed (fingerprint := "1464190755733159356")
*Theorem: an external call lets escape all it reaches.* Every allocation
reachable from $`\vec{q}` in $`s` is in
$`\mathrm{escapeCall}_s(\vec{q}).\mathrm{escaped}`. With the theorem
above, the allocations that have a handle after the call are exactly the
reachable ones.
:::
