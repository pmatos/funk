import VersoManual
import Fir.Execution.RunStart
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the memories a run starts with, which
renders `Fir.Execution.RunStart` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The memories a run starts with: readable blocks" =>

:::moduleDocs (fingerprint := "5482329221718497856")
:::

:::readable Fir.StartAlloc.block Fir.Memory.Memories.place Fir.Memory.Memories.ofStarts Fir.RunItems.start (pin := Fir.Memory.Memories.empty) (fingerprint := "17821042395608482575")
*Definition: the memories a run starts with.* A starting allocation
$`(n, k, \alpha, c, \vec{x})` gives, in a memory of $`u`-bit units, the
live block $`(k, \alpha, \vec{x}_u, \mathsf{true}, \bot, c)`: of its kind
and alignment, with its units at that width, no address yet, and constant
when $`c` is. Placing a block $`b` in the memory $`x` of the memories
$`S` makes it the next allocation of $`x`, $`S[x := S(x)~b]`, and keeps
the frames and each memory's count of integers turned back into pointers.

From the starting allocations $`A`, and a map $`\nu` from the numbers of
the data layout's memories to the run's memories, the memories
$`\mathrm{start}_\nu(A)` place each allocation of $`A`, in order, in the
memory $`\nu(n)` of its number $`n`, starting from the empty memories,
outside every call and with no integer turned back into a pointer yet. An allocation of a number that $`\nu` names no memory
for is left out. So in each memory the allocations of $`A` take the ids
from $`0` up, in the order of $`A`, before anything the run allocates.

A run of the dialect $`d` that names the dialect's memory $`x` as
$`\rho(x)`, whose entry is $`\mathit{lay}(\rho(x))`, and gives the items
$`L`, starts from $`\mathrm{start}_\nu(L.\mathrm{starts})`, where
$`\nu(n) = \rho(x)` for the dialect's memory $`x` that the layout numbers
$`n`, if it has one. For the core, $`\nu = \rho`; for a sum, the base's
memories. A dialect with no numbered memory starts from the empty
memories, as every run did before globals.
:::

:::readable Fir.Memory.Memories.place_frames Fir.Memory.Memories.ofStarts_frames Fir.Memory.Memories.ofStarts_none Fir.RunItems.start_unnumbered Fir.RunItems.start_nil Fir.RunItems.start_withAddrs Fir.Global.start_units_length (fingerprint := "18371459671141773741")
*Theorems: what the starting memories are.* Placing a block keeps the
frames, so the starting memories have none: a run starts outside every
call, and the interpreter enters the frame of the function it runs, which
frees none of them. Allocations of numbers that name no memory leave the
memories empty, so a run of a dialect with no numbered memory, or of
items that list no allocation, starts from the empty memories. An address
policy changes no starting allocation. A global starts with exactly as
many units as its size: its initializer's units, cut to the size, then
zeros up to it.
:::
