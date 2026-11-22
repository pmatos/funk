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

:::moduleDocs (fingerprint := "15852211188585987574")
:::

:::readable Fir.Memory.Memories (fingerprint := "16888250131718672919")
*Definition: the memories of a run.* For memories named by $`X`, where the
memory $`x` has units of $`u(x)` bits, the memories of a run are a triple
$`(T, \mathit{fr}^*, c)`:

```grammar Fir.Memory.Memories
\mathit{mems}
table,frames,rebuilds   (T, \mathit{fr}^*, c)
```

* $`T` is the table of the memories: a list of pairs $`(x, m)`, the name
  $`x` and a {ref "The-fir-specification--Memory--The-memory-model"}[memory]
  $`m` whose units are $`u(x)` bits wide. The memory $`x` of the run,
  $`\mathit{mem}(x)`, is the first memory of that name in the table, and
  the empty memory when the table has none;
* $`\mathit{fr}^*` is a stack of frames, the innermost first, one for each
  call that has not returned. A frame is a list of pairs $`(x, a)`: the
  stack allocation $`a` of the memory $`x`, made by its call;
* $`c` counts, for each memory $`x`, the integers the run has turned back
  into pointers of $`x`, $`c(x)`, which the
  {ref "The-fir-specification--Memory--Address-resolvers"}[resolver] of
  $`x` sees at each call.

No width is fixed here: the module's data layout gives each memory its
unit, and the memories are written for any. The table holds each name at
most once, so finding a memory looks at no more entries than the run has
memories, however many updates came before.
:::

:::readable Fir.Memory.Memories.empty (fingerprint := "13971899226138868642")
*Definition: no memory yet.* Before a run starts, the table is empty, so
every memory is empty, there is no frame, and no integer has been turned
back into a pointer: $`(\epsilon, \epsilon, x \mapsto 0)`.
:::

:::readable Fir.Memory.Memories.enter (fingerprint := "6877764141344344430")
*Definition: entering a call.* Entering a call pushes an empty frame:
$`\mathrm{enter}(T, \mathit{fr}^*, c) = (T, \epsilon~\mathit{fr}^*, c)`.
:::

:::readable Fir.Memory.Memories.lookup Fir.Memory.Memories.mem (fingerprint := "13526315122793642062")
*Definition: the memory of a name.* The memory $`x` of a table is the
memory of its first pair named $`x`, and the empty memory when no pair is:

$$`\mathrm{lookup}_x(\epsilon) = \emptyset \qquad \mathrm{lookup}_x((y, m)~T) = \begin{cases} m & \text{if } y = x \\ \mathrm{lookup}_x(T) & \text{otherwise} \end{cases}`

The memory $`x` of the memories $`(T, \mathit{fr}^*, c)` of a run,
$`\mathit{mem}(x)`, is $`\mathrm{lookup}_x(T)`.
:::

:::readable Fir.Memory.Memories.load (fingerprint := "10112896710225288711")
*Definition: a load from one memory.* Loading $`n` units of the memory
$`x` through the pointer $`p`, aligned to $`\alpha` units, is the memory
model's
{ref "The-fir-specification--Memory--The-memory-model"}[aligned load] of
$`n` units through $`p` in $`\mathit{mem}(x)`: the units, or the fault
that makes the load UB.
:::

:::readable Fir.Memory.Memories.set (fingerprint := "7061823943516504143")
*Definition: replacing one memory.* $`S[x := m]` is $`S` with the memory
$`x` replaced by $`m`, every other memory, the frames and the count as
they were. The pair $`(x, m)` goes first in the table, and every older
pair named $`x` is dropped from it:
$`(T, \mathit{fr}^*, c)[x := m] = ((x, m)~T', \mathit{fr}^*, c)`, where $`T'`
is $`T` without its pairs named $`x`.
:::

:::readable Fir.Memory.Memories.record (fingerprint := "13605680622301485857")
*Definition: recording a stack allocation.* Recording the allocation $`a`
of the memory $`x` adds $`(x, a)` to the innermost frame. Outside every
call there is no frame, and nothing is recorded.
:::

:::readable Fir.Memory.Memories.alloc (fingerprint := "2210556411997624409")
*Definition: allocating in one memory.* Allocating $`n` units of kind
$`k`, aligned to $`\alpha` units, in the memory $`x` is the memory
model's allocation in
$`\mathit{mem}(x)`, which gives the pointer $`(|\mathit{mem}(x)|, 0)` to
the new allocation. A stack allocation is then recorded in the innermost
frame, so that it is freed when its call returns; an allocation of
another kind is in no frame.
:::

:::readable Fir.Memory.Memories.free (fingerprint := "10185952607630522104")
*Definition: freeing in one memory.* Freeing the allocation $`a` of the
memory $`x` is the memory model's free of $`a` in $`\mathit{mem}(x)`.
:::

:::readable Fir.Memory.Memories.store (fingerprint := "11826908114044317332")
*Definition: a store to one memory.* Storing the units $`\vec{y}` to the
memory $`x` through $`p`, aligned to $`\alpha` units, is the memory
model's aligned store in $`\mathit{mem}(x)`: the memories with that
memory stored to, or the fault that makes the store UB.
:::

:::readable Fir.Memory.Memories.freeAll (fingerprint := "1105949709820377174")
*Definition: freeing a list.* Freeing the list
$`(x_1, a_1) \dots (x_n, a_n)` frees $`a_1` of $`x_1`, then the others in
order.
:::

:::readable Fir.Memory.Memories.exit (fingerprint := "12035581706300799354")
*Definition: leaving a call.* Leaving a call frees every allocation of the
innermost frame and pops it:

$$`\mathrm{exit}(T, \mathit{fr}~\mathit{fr}^*, c) = \mathrm{freeAll}((T, \mathit{fr}^*, c), \mathit{fr})`

Outside every call there is no frame, and leaving changes nothing.
Freeing never faults, so neither does leaving a call.
:::
