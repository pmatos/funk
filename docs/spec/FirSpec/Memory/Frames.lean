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

:::moduleDocs (fingerprint := "10112496316411910550")
:::

:::readable Fir.Memory.Memories (fingerprint := "12347572415275710577")
*Definition: the memories of a run.* For memories named by $`X`, where the
memory $`x` has units of $`u(x)` bits, the memories of a run are a pair
$`(\mathit{mem}, \mathit{frames})`:

```grammar Fir.Memory.Memories
\mathit{mems}
mem,frames   (\mathit{mem}, \mathit{fr}^*)
```

* $`\mathit{mem}(x)` is the memory $`x`, a
  {ref "The-fir-specification--Memory--The-memory-model"}[memory] whose
  units are $`u(x)` bits wide;
* $`\mathit{fr}^*` is a stack of frames, the innermost first, one for each
  call that has not returned. A frame is a list of pairs $`(x, a)`: the
  stack allocation $`a` of the memory $`x`, made by its call.

No width is fixed here: the module's data layout gives each memory its
unit, and the memories are written for any.
:::

:::readable Fir.Memory.Memories.empty (fingerprint := "13895302857523309904")
*Definition: no memory yet.* Before a run starts, every memory is empty,
and there is no frame: $`(x \mapsto \emptyset, \epsilon)`.
:::

:::readable Fir.Memory.Memories.enter (fingerprint := "13182771099878607732")
*Definition: entering a call.* Entering a call pushes an empty frame:
$`\mathrm{enter}(\mathit{mem}, \mathit{fr}^*) = (\mathit{mem}, \epsilon~\mathit{fr}^*)`.
:::

:::readable Fir.Memory.Memories.load (fingerprint := "14713560683503428408")
*Definition: a load from one memory.* Loading $`n` units of the memory
$`x` through the pointer $`p` is the memory model's load of $`n` units
through $`p` in $`\mathit{mem}(x)`: the units, or the fault that makes the
load UB.
:::

:::readable Fir.Memory.Memories.set (fingerprint := "16632318407637454539")
*Definition: replacing one memory.* $`S[x := m]` is $`S` with the memory
$`x` replaced by $`m`, every other memory and the frames as they were.
:::

:::readable Fir.Memory.Memories.record (fingerprint := "10199683790596524269")
*Definition: recording a stack allocation.* Recording the allocation $`a`
of the memory $`x` adds $`(x, a)` to the innermost frame. Outside every
call there is no frame, and nothing is recorded.
:::

:::readable Fir.Memory.Memories.alloc (fingerprint := "3905892275111002209")
*Definition: allocating in one memory.* Allocating $`n` units of kind
$`k` in the memory $`x` is the memory model's allocation in
$`\mathit{mem}(x)`, which gives the pointer $`(|\mathit{mem}(x)|, 0)` to
the new allocation. A stack allocation is then recorded in the innermost
frame, so that it is freed when its call returns; an allocation of
another kind is in no frame.
:::

:::readable Fir.Memory.Memories.free (fingerprint := "5270964239054137916")
*Definition: freeing in one memory.* Freeing the allocation $`a` of the
memory $`x` is the memory model's free of $`a` in $`\mathit{mem}(x)`.
:::

:::readable Fir.Memory.Memories.store (fingerprint := "17372147829549218195")
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

:::readable Fir.Memory.Memories.exit (fingerprint := "4448542500945856441")
*Definition: leaving a call.* Leaving a call frees every allocation of the
innermost frame and pops it:

$$`\mathrm{exit}(\mathit{mem}, \mathit{fr}~\mathit{fr}^*) = \mathrm{freeAll}((\mathit{mem}, \mathit{fr}^*), \mathit{fr})`

Outside every call there is no frame, and leaving changes nothing.
Freeing never faults, so neither does leaving a call.
:::
