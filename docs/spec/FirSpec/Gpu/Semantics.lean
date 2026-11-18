import VersoManual
import Fir.Gpu.Semantics
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the rules of `gpu`, which renders
`Fir.Gpu.Semantics` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "The GPU dialect's rules: readable blocks" =>

:::moduleDocs (fingerprint := "2998706189026444271")
:::

:::readable Fir.Gpu.WorkItem Fir.Gpu.WorkItem.answer (fingerprint := "6943720344622700870")
*Definition: the work-item.* A run of a kernel takes the work-item that it
runs as its input, beside its arguments. A work-item $`w` gives four
numbers in each dimension $`d`: its id within its work-group,
$`\mathrm{id}_w(d)`, the id of its work-group, $`\mathrm{group}_w(d)`, the
number of work-items in a work-group, $`\mathrm{size}_w(d)`, and the number
of work-groups, $`\mathrm{count}_w(d)`. The answer of $`w` to a question
in a dimension is the number that the question names:
$`\mathsf{work\_item\_id}` the id, $`\mathsf{work\_group\_id}` the group's
id, $`\mathsf{work\_group\_size}` the size and $`\mathsf{num\_work\_groups}`
the count.
:::

:::readable Fir.Gpu.WorkItem.Valid Fir.Gpu.instDecidableValid (fingerprint := "1712488518336837127")
*Definition: a work-item of its grid.* A work-item $`w` is one of its grid
when, in each dimension $`d`,
$`\mathrm{id}_w(d) < \mathrm{size}_w(d)`,
$`\mathrm{group}_w(d) < \mathrm{count}_w(d)`, and the size and the count
are below $`2^{32}`, so each number is the unsigned value of an `i32`. It
can be decided. `fir-ref run` runs only such a work-item; the rules and the
theorems below hold at every work-item.
:::

:::readable Fir.Gpu.WorkItem.single Fir.Gpu.WorkItem.single_valid (fingerprint := "552102532973513732")
*Definition: the one work-item of a grid of one.* The work-item whose ids
are all $`0` and whose sizes and counts are all $`1`. It is one of its grid,
and it is the one that `fir-ref run` runs when no option gives another.
:::

:::readable Fir.Gpu.queryResults Fir.Gpu.instDialectDenote (fingerprint := "7226692803670689930")
*Definition: the rules of `gpu` in the set monad.* At a work-item $`w`, the op
$`\mathsf{query}_N~q~d` takes no operand and gives one result, the
answer of $`w` to $`q` in $`d`, as an integer of $`N` bits, modulo
$`2^N`:

$$`\mathsf{query}_N~q~d \Downarrow (\mathrm{answer}_w(q, d) \bmod 2^N)`

It is never poison and never UB, and it makes no choice: it gives its
result at once. An allocation needs memory, so in the set monad it has no
outcome, as `alloca` has none. No op of
`gpu` is a terminator, so the interpreter never asks where one goes; it is
written as a return.
:::

:::readable Fir.Gpu.allocRule Fir.Gpu.memDenoteIn Fir.Gpu.instDialectMemDenote Fir.Gpu.instDialectCall (pin := Fir.Core.allocaShape) (fingerprint := "15517050764245440989")
*Definition: the rules of `gpu` with memory, and its calls.* Where a run's
memories have the layout entries $`\mathit{lay}` and the run names `gpu`'s
memory $`x` as $`\rho(x)`, a question gives its results and keeps the
memories, and $`\mathsf{alloc}_n~t~c~a` allocates in the memory
$`\rho(n)` the units and alignment that `alloca` would take there,
$`\mathrm{allocaShape}(t, c, a, n)`, with the kind $`\mathsf{global}`, and
gives the pointer $`p` to the allocation:

$$`\langle \mathsf{alloc}_n~t~c~a, S\rangle \Downarrow \langle [p], S' \rangle \quad\text{where}\quad (p, S') = S.\mathrm{alloc}(\rho(n), \mathsf{global}, \mathrm{allocaShape}(t, c, a, n))`

A global allocation is recorded in no frame, so no call frees it when it
returns: it lives until the run ends. A run is the run of one work-item,
so the allocation lives from the op to the end of the kernel's run,
whichever function of the device module ran the op, and each run of the op
makes a new allocation. How the work-items of one work-group share one
allocation is left for when several work-items run. No op of `gpu` calls a
function.
:::

:::readable Fir.Gpu.query_denote_eq Fir.Gpu.queryResults_noPoison Fir.Gpu.queryResults_refl (fingerprint := "175932838683491064")
*Lemmas: what a question gives.* In the set monad, a question ends only
with its results. Its results hold no poison, and they refine themselves.
:::

:::readable Fir.Gpu.query_liftsSetM (fingerprint := "7883783630560395389")
*Lemma: a question is tied.* At every layout and naming of `gpu`'s
memories, a question runs with memory by its rule in the set monad and
keeps the memories, as a core op that touches no memory does.
:::

:::readable Fir.Gpu.query_propagates Fir.Gpu.query_monotone Fir.Gpu.query_total Fir.Gpu.query_returnsOnDefined Fir.Gpu.query_neverUBSetM Fir.Gpu.query_makesNoPoisonSetM (fingerprint := "6257091572041050134")
*Lemmas: a question meets the obligations in the set monad.* At every
work-item, a question propagates poison, since it takes no operand and is
never UB; it is monotone at every width, since it gives the same result
whatever its operands; it is total; it returns a result on the empty,
defined operand vector; it never ends in UB; and it makes no poison. With
its tie, each of these gives the obligation with memory (the section on
work-group allocation). `gpu` as a whole meets no lawful class of the set
monad, since an allocation has no outcome there, as the core does not.
:::
