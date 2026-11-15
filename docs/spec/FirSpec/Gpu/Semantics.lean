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

:::moduleDocs (fingerprint := "2991841930195314186")
:::

:::readable Fir.Gpu.WorkItem Fir.Gpu.WorkItem.answer (fingerprint := "18027391566621417795")
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

:::readable Fir.Gpu.Op.results Fir.Gpu.denoteIn Fir.Gpu.instDialectDenote (fingerprint := "12468139233404181554")
*Definition: the rules of `gpu`.* At a work-item $`w`, the op
$`\mathsf{query}_N~q~d` takes no operand and gives one result, the
answer of $`w` to $`q` in $`d`, as an integer of $`N` bits, modulo
$`2^N`:

$$`\mathsf{query}_N~q~d \Downarrow (\mathrm{answer}_w(q, d) \bmod 2^N)`

It is never poison and never UB, and it makes no choice: it is the same
in every monad, where it gives its result at once. No op of `gpu` is a
terminator, so the interpreter never asks where one goes; it is written as
a return.
:::

:::readable Fir.Gpu.instDialectMemDenote Fir.Gpu.instLiftsSetM Fir.Gpu.instDialectCall (fingerprint := "57592451508523719")
*Definition: `gpu` with memory, and its calls.* No op of `gpu` touches
memory: wherever a run names its memories, each op runs by its rule in the
set monad and keeps the memories, so its semantics with memory lifts its
semantics in the set monad. No op of `gpu` calls a function.
:::

:::readable Fir.Gpu.denote_eq Fir.Gpu.results_noPoison Fir.Gpu.results_refl (fingerprint := "16039041179146263412")
*Lemmas: what an op of `gpu` gives.* In the set monad, an op of `gpu` ends
only with its results. Its results hold no poison, and they refine
themselves.
:::

:::readable Fir.Gpu.propagates Fir.Gpu.Op.monotone Fir.Gpu.lawful (fingerprint := "6693562354796987970")
*Theorems: `gpu` is lawful.* At every work-item, each op of `gpu`
propagates poison, since it takes no operand and is never UB; it returns a
result on the empty, defined operand vector; it is total; and it is
monotone at every width, since it gives the same result whatever its
operands. A poison value of a valid type, a core type, is refined by every
value of its type. So `gpu` meets the poison obligations.
:::

:::readable Fir.Gpu.lawfulDialectEffects (fingerprint := "8033647288015854687")
*Theorem: the effect set of `gpu` is sound.* At every work-item, each op of
`gpu`, which declares the empty effect set, is never UB, makes no poison on
operands with no poison, is not a terminator, and, wherever a run names its
memories, writes, reads and allocates in no memory. So the dialect's
declaration of its effects is proved.
:::

:::readable Fir.Gpu.lawfulTotal Fir.Gpu.lawfulMonotone Fir.Gpu.lawfulMemPoison (fingerprint := "7232679307526935766")
*Theorems: `gpu` is lawful with memory.* `gpu` is lawful and lifts the set
monad, so at every work-item it is lawful in its totality, its monotonicity
and its poison with memory.
:::
