import VersoManual
import Fir.Memory.FrameLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on frame laws, which renders
`Fir.Memory.FrameLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Frame laws: readable blocks" =>

:::moduleDocs (fingerprint := "8614347794442316598")
:::

:::readable Fir.Memory.Memories.enter_mem Fir.Memory.Memories.exit_enter (fingerprint := "11872330539158653898")
*Theorem: entering a call touches no memory.* Entering a call changes no
memory, and entering a call then leaving it at once gives back the
memories as they were: $`\mathrm{exit}(\mathrm{enter}(S)) = S`.
:::

:::readable Fir.Memory.Memories.set_mem_self Fir.Memory.Memories.set_mem_ne Fir.Memory.Memories.set_frames (fingerprint := "14752833637550411569")
*Theorem: replacing one memory.* In $`S[x := m]`, the memory $`x` is
$`m`, every memory $`y \neq x` is $`S`'s, and the frames are $`S`'s.
:::

:::readable Fir.Memory.Memories.kill_kill (fingerprint := "12794855804287308356")
*Theorem: freeing a freed block changes nothing.* Killing a killed block
gives the killed block: $`\mathrm{kill}(\mathrm{kill}(b)) = \mathrm{kill}(b)`.
:::

:::readable Fir.Memory.Memories.free_get Fir.Memory.Memories.free_length (fingerprint := "5944758421440549963")
*Theorem: a free kills only its own allocation.* After freeing $`b` of
$`y`, the allocation $`a` of $`x` is $`\mathrm{kill}` of what it was when
$`(y, b) = (x, a)`, and as it was otherwise. No memory gains or loses an
allocation.
:::

:::readable Fir.Memory.Memories.freeAll_get Fir.Memory.Memories.freeAll_length Fir.Memory.Memories.freeAll_frames (fingerprint := "17629710118196293691")
*Theorem: freeing a list kills exactly what it lists.* After freeing the
list $`l`, the allocation $`a` of $`x` is killed when $`(x, a) \in l`, and
as it was otherwise. No memory gains or loses an allocation, and the
frames stay as they were.
:::

:::readable Fir.Memory.Memories.exit_frames Fir.Memory.Memories.exit_get Fir.Memory.Memories.exit_length (fingerprint := "9530880913325362074")
*Theorem: leaving a call frees exactly its frame.* When the frames of
$`S` are $`\mathit{fr}~\mathit{fr}^*`, leaving the call pops
$`\mathit{fr}`, so the frames are $`\mathit{fr}^*`; it kills the
allocation $`a` of $`x` when $`(x, a) \in \mathit{fr}`, and leaves every
other allocation, of every memory, as it was. Leaving a call never adds
or removes an allocation.
:::

:::readable Fir.Memory.Memories.record_mem Fir.Memory.Memories.alloc_fst Fir.Memory.Memories.alloc_mem_self Fir.Memory.Memories.alloc_mem_ne (fingerprint := "7246019016461453106")
*Theorem: an allocation touches only its own memory.* Recording an
allocation changes no memory. Allocating in the memory $`x` gives the
pointer $`(|\mathit{mem}(x)|, 0)`, makes $`x` the memory model's
allocation in $`\mathit{mem}(x)`, and leaves every other memory as it
was.
:::

:::readable Fir.Memory.Memories.alloc_stack_frames Fir.Memory.Memories.alloc_frames (fingerprint := "14879741181503107876")
*Theorem: only a stack allocation joins a frame.* When the frames of
$`S` are $`\mathit{fr}~\mathit{fr}^*`, a stack allocation in $`x` makes
them $`((x, |\mathit{mem}(x)|)~\mathit{fr})~\mathit{fr}^*`. An allocation
of any other kind leaves the frames as they were.
:::

:::readable Fir.Memory.Memories.enter_alloc_exit Fir.Memory.Memories.enter_alloc_exit_load (fingerprint := "5891743082393682445")
*Theorem: a call's stack allocation is freed when the call returns.* Enter
a call, allocate $`n` units on the stack of the memory $`x`, and leave
the call. Then the new allocation, $`|\mathit{mem}(x)|`, is a block of the
stack kind, of $`n` poisons, no longer live, and every load from it, at
any offset and of any size, faults with $`\mathsf{freed}`
(ADR-2026-11-09-1548).
:::
