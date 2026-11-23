import VersoManual
import Fir.Execution.TraceEscape
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on what an external call lets escape,
which renders `Fir.Execution.TraceEscape` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "What an external call lets escape: readable blocks" =>

:::moduleDocs (fingerprint := "12609950944018777986")
:::

:::readable Fir.TraceState.Live Fir.TraceState.instDecidableLive Fir.TraceState.escapePtr Fir.TraceState.escapePtrs Fir.TraceState.ptrsIn (fingerprint := "3223482053865899791")
*Definition: letting a pointer's allocation escape.* The allocation $`a`
of the memory $`x` is live in the traced state $`s` when the memory has
an allocation $`a` that is not freed. A pointer $`p` of the memory
numbered $`n`, where that memory is $`\mu(n)`, lets escape the
allocation it has provenance for, $`(\mu(n), p.\mathrm{prov})`, when that
allocation is live: it joins the end of the escaped list unless it is
there already. A pointer with no provenance lets nothing escape.
$`\mathrm{escape}_s(q_1, \dots, q_k)` lets the pointers $`q_1, \dots, q_k`
do so, in order. $`\mathrm{ptrs}_s(x, a)` lists the pointers that the
units of a live allocation hold, in the order of its units, and none of an
allocation that is not live.
:::

:::readable Fir.Memory.Memories.allocs Fir.Memory.Memories.mem_lookup_allocs Fir.Memory.Memories.mem_allocs Fir.TraceState.unescaped Fir.List.filter_length_le_of_imp Fir.List.filter_length_lt_of_imp (fingerprint := "1637773271867210751")
*Definition: the allocations that may still escape.* The allocations of
the memories' table are those of each memory it holds, and every
allocation of a memory is one of them. $`\mathrm{unescaped}(s)` counts
the allocations of the table that are not in the escaped list. A filter
by a test keeps no more elements than a filter by a weaker test, and fewer
when the weaker one keeps an element that the first drops. A filter
by a test keeps no more elements than a filter by a weaker test, and fewer
when the weaker one keeps an element that the first drops.
:::

:::readable Fir.TraceState.escape_cases Fir.TraceState.escapePtr_cases Fir.TraceState.escapePtr_mem Fir.TraceState.escapePtrs_mem Fir.TraceState.escapePtr_prefix Fir.TraceState.escapePtrs_prefix Fir.TraceState.escapePtrs_cases (fingerprint := "10795533896428786864")
*Theorems: escaping only adds.* Letting an allocation escape keeps the
memories, and either changes nothing or adds at the end of the escaped
list a live allocation that was not in it. So letting pointers'
allocations escape keeps the memories, keeps the escaped list as a
prefix, and either changes nothing or lowers $`\mathrm{unescaped}(s)`.
:::

:::readable Fir.TraceState.reach Fir.TraceState.escapeCall (fingerprint := "16949573049359115466")
*Definition: what an external call lets escape.* The walk from the handle
$`k` takes the escaped allocation of handle $`k`, if any, lets escape the
pointers its units hold, in order, and goes on from the handle $`k + 1`:

$$`\mathrm{reach}_s(k) = \begin{cases} \mathrm{reach}_{s'}(k + 1) & k < |s.\mathrm{escaped}|,\ s' = \mathrm{escape}_s(\mathrm{ptrs}_s(s.\mathrm{escaped}_k)) \\ s & \text{otherwise} \end{cases}`

It ends: each step either lowers $`\mathrm{unescaped}(s)` or leaves the
list and moves $`k` towards its end. An external call on arguments that
hold the pointers $`\vec{q}` lets escape

$$`\mathrm{escapeCall}_s(\vec{q}) = \mathrm{reach}_{\mathrm{escape}_s(\vec{q})}(0)`

the pointer arguments first, then, handle by handle, what escaped memory
points into. The order comes from positions, never from allocation ids.
:::

:::readable Fir.TraceState.reach_mem_prefix Fir.TraceState.escapeCall_mem Fir.TraceState.escapeCall_prefix (fingerprint := "14357844300769900380")
*Theorems: an external call keeps the memories and the handles.* What an
external call lets escape keeps the memories, and the escaped list it
starts from is a prefix of the one it gives: each allocation that had
escaped keeps its handle.
:::
