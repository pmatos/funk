import VersoManual
import Fir.Memory.Frames
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the memories of a run, which renders
`Fir.Memory.Frames` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "The memories of a run: readable blocks" =>

:::moduleDocs (fingerprint := "11371100963345902637")
:::

:::readable Fir.Memory.Memories (fingerprint := "11688577113277533231")
*Definition: the memories of a run.* For memories named by $`X`, where the
memory $`x` has units of $`u(x)` bits, the memories of a run are a pair
$`(T, \mathit{fr}^*)`:

```grammar Fir.Memory.Memories
\mathit{mems}
table,frames   (T, \mathit{fr}^*)
```

* $`T` is the table of the memories: a list of pairs $`(x, m)`, the name
  $`x` and a {ref "The-fir-specification--Memory--The-memory-model"}[memory]
  $`m` whose units are $`u(x)` bits wide. The memory $`x` of the run,
  $`\mathit{mem}(x)`, is the first memory of that name in the table, and
  the empty memory when the table has none;
* $`\mathit{fr}^*` is a stack of frames, the innermost first, one for each
  call that has not returned. A frame is a list of pairs $`(x, a)`: the
  stack allocation $`a` of the memory $`x`, made by its call.

No width is fixed here: the module's data layout gives each memory its
unit, and the memories are written for any. The table holds each name at
most once, so finding a memory looks at no more entries than the run has
memories, however many updates came before.
:::

:::readable Fir.Memory.Memories.empty (fingerprint := "10913081583095296761")
*Definition: no memory yet.* Before a run starts, the table is empty, so
every memory is empty, and there is no frame: $`(\epsilon, \epsilon)`.
:::

:::readable Fir.Memory.Memories.enter (fingerprint := "890583241385760010")
*Definition: entering a call.* Entering a call pushes an empty frame:
$`\mathrm{enter}(T, \mathit{fr}^*) = (T, \epsilon~\mathit{fr}^*)`.
:::

:::readable Fir.Memory.Memories.lookup Fir.Memory.Memories.mem (fingerprint := "7512583844530461172")
*Definition: the memory of a name.* The memory $`x` of a table is the
memory of its first pair named $`x`, and the empty memory when no pair is:

$$`\mathrm{lookup}_x(\epsilon) = \emptyset \qquad \mathrm{lookup}_x((y, m)~T) = \begin{cases} m & \text{if } y = x \\ \mathrm{lookup}_x(T) & \text{otherwise} \end{cases}`

The memory $`x` of the memories $`(T, \mathit{fr}^*)` of a run,
$`\mathit{mem}(x)`, is $`\mathrm{lookup}_x(T)`.
:::

:::readable Fir.Memory.Memories.load (fingerprint := "3342685884046637813")
*Definition: a load from one memory.* Loading $`n` units of the memory
$`x` through the pointer $`p` is the memory model's load of $`n` units
through $`p` in $`\mathit{mem}(x)`: the units, or the fault that makes the
load UB.
:::

:::readable Fir.Memory.Memories.set (fingerprint := "16196087832232445707")
*Definition: replacing one memory.* $`S[x := m]` is $`S` with the memory
$`x` replaced by $`m`, every other memory and the frames as they were. The
pair $`(x, m)` goes first in the table, and every older pair named $`x`
is dropped from it:
$`(T, \mathit{fr}^*)[x := m] = ((x, m)~T', \mathit{fr}^*)`, where $`T'`
is $`T` without its pairs named $`x`.
:::

:::readable Fir.Memory.Memories.record (fingerprint := "16418323436834618849")
*Definition: recording a stack allocation.* Recording the allocation $`a`
of the memory $`x` adds $`(x, a)` to the innermost frame. Outside every
call there is no frame, and nothing is recorded.
:::

:::readable Fir.Memory.Memories.alloc (fingerprint := "9668364342418105557")
*Definition: allocating in one memory.* Allocating $`n` units of kind
$`k` in the memory $`x` is the memory model's allocation in
$`\mathit{mem}(x)`, which gives the pointer $`(|\mathit{mem}(x)|, 0)` to
the new allocation. A stack allocation is then recorded in the innermost
frame, so that it is freed when its call returns; an allocation of
another kind is in no frame.
:::

:::readable Fir.Memory.Memories.free (fingerprint := "10185952607630522104")
*Definition: freeing in one memory.* Freeing the allocation $`a` of the
memory $`x` is the memory model's free of $`a` in $`\mathit{mem}(x)`.
:::

:::readable Fir.Memory.Memories.store (fingerprint := "6751036384068824913")
*Definition: a store to one memory.* Storing the units $`\vec{y}` to the
memory $`x` through $`p` is the memory model's store in
$`\mathit{mem}(x)`: the memories with that memory stored to, or the fault
that makes the store UB.
:::

:::readable Fir.Memory.Memories.freeAll (fingerprint := "14734991384166219062")
*Definition: freeing a list.* Freeing the list
$`(x_1, a_1) \dots (x_n, a_n)` frees $`a_1` of $`x_1`, then the others in
order.
:::

:::readable Fir.Memory.Memories.exit (fingerprint := "8548377517380936683")
*Definition: leaving a call.* Leaving a call frees every allocation of the
innermost frame and pops it:

$$`\mathrm{exit}(T, \mathit{fr}~\mathit{fr}^*) = \mathrm{freeAll}((T, \mathit{fr}^*), \mathit{fr})`

Outside every call there is no frame, and leaving changes nothing.
Freeing never faults, so neither does leaving a call.
:::
