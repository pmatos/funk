import VersoManual
import Fir.Execution.MemoryObligations
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on memory obligations, which renders
`Fir.Execution.MemoryObligations` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Memory obligations: readable blocks" =>

:::moduleDocs (fingerprint := "17710123599665356057")
:::

:::readable Fir.Memory.Memory.allocs Fir.Memory.Memory.contents Fir.Memory.Memory.unitAt (fingerprint := "2324173610234647755")
*Definition: what a memory holds.* For a memory $`M` with the blocks
$`b_0 \ldots b_{k-1}`:

* its _allocations_ are the kind, size and liveness of each block, in
  order: $`\mathrm{allocs}(M) = (b_i.\mathit{kind}, |b_i.\mathit{units}|, b_i.\mathit{live})_{i < k}`;
* its _contents_ are the units of each block, in order:
  $`\mathrm{contents}(M) = (b_i.\mathit{units})_{i < k}`;
* $`M[a, i]` is the unit at offset $`i` of the allocation $`a`, or
  nothing when there is none.
:::

:::readable Fir.Memory.Memories.framesOf Fir.Memory.Memories.AgreeOff (fingerprint := "8038084194344165965")
*Definition: the frames of a memory, and agreeing off a memory.* The
frames of the memory $`x` in $`S` list, for each frame of $`S`, innermost
first, the ids of the stack allocations of $`x` that it holds. Two
memories of a run $`S_1` and $`S_2` _agree off_ $`x` when
$`S_1.\mathit{frames} = S_2.\mathit{frames}`, $`S_1.\mathit{mem}(y) = S_2.\mathit{mem}(y)`
for every $`y \neq x`, and
$`\mathrm{allocs}(S_1.\mathit{mem}(x)) = \mathrm{allocs}(S_2.\mathit{mem}(x))`.
:::

:::readable Fir.WritesNot Fir.AllocatesNot (fingerprint := "18251249360256599985")
*Definition: no write, and no allocation.* A computation $`c` of the
state layer over the set monad _writes no unit of_ $`x` when every way it
ends, $`\mathsf{ok}~(a, S') \in c(S)`, keeps the contents of $`x` as a
prefix: $`\mathrm{contents}(S.\mathit{mem}(x))` is a prefix of
$`\mathrm{contents}(S'.\mathit{mem}(x))`. So each allocation of $`x` that
was there holds the units it held, and new allocations may follow.

It _neither allocates nor frees in_ $`x` when every way it ends keeps the
allocations of $`x` and the frames of $`x`:
$`\mathrm{allocs}(S'.\mathit{mem}(x)) = \mathrm{allocs}(S.\mathit{mem}(x))`,
and the frames of $`x` in $`S'` are those in $`S`.

A computation that neither writes nor allocates in $`x` ends with $`x` as
it was. UB ends a path and shows no memory, so both speak only of the
paths that end.
:::

:::readable Fir.ReadsNot.Match Fir.ReadsNot (fingerprint := "2639600274913278735")
*Definition: no read.* A computation $`c` _does not read_ $`x` when it does
not depend on the units of $`x`. For all memories of a run $`S` and every
memory $`m` with $`\mathrm{allocs}(m) = \mathrm{allocs}(S.\mathit{mem}(x))`,
each way that $`c` may end from $`S` has a _match_ among the ways it may
end from $`S[x := m]`:

* $`\mathsf{ub}~r` matches $`\mathsf{ub}~r`, for the same reason $`r`;
* $`\mathsf{ok}~(a, S_1)` matches $`\mathsf{ok}~(a, S_2)`, with the same
  result $`a`, when $`S_1` and $`S_2` agree off $`x`, and each unit of
  $`x` is the same in both or is in each the unit it was before: for all
  $`b` and $`i`, $`S_1.\mathit{mem}(x)[b, i] = S_2.\mathit{mem}(x)[b, i]`,
  or $`S_1.\mathit{mem}(x)[b, i] = S.\mathit{mem}(x)[b, i]` and
  $`S_2.\mathit{mem}(x)[b, i] = m[b, i]`.

A load from $`x` gives different units from $`S` and from $`S[x := m]`,
so it reads $`x`. A store to $`x` writes the same units in both and leaves
the rest, so it does not read $`x`: whether it faults depends only on the
allocations of $`x`, which $`m` keeps.
:::

:::readable Fir.DialectMemDenote Fir.OwnRuleHas (fingerprint := "379604914047239213")
*Definition: a dialect's semantics with memory.* A dialect gives each op a
semantics in the state layer over the set monad _wherever a run names its
memories_: for every type $`N` of a run's memory names, the unit width of
each, and every map $`\rho` from the dialect's memory names to $`N`, a
semantics of its ops in the state layer over the memories named by $`N`.
The op names the dialect's memory $`x` as the run's memory $`\rho(x)`.

What an op $`o` runs by its own rule at $`\rho` _has a property_ $`P` when,
on every operand vector $`\vec{v}`, $`P(\mathrm{denote}_o(\vec{v}))` holds
if $`o` is not a terminator, and $`P(\mathrm{exit}_o(\vec{v}))` holds if it
is.
:::
