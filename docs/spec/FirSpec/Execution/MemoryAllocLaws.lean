import VersoManual
import Fir.Execution.MemoryAllocLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on allocation in the state layer, which
renders `Fir.Execution.MemoryAllocLaws` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Allocation in the state layer: readable blocks" =>

:::moduleDocs (fingerprint := "16258933277607196906")
:::

:::readable Fir.Memory.Memory.unitAt_alloc_lt Fir.Memory.Memory.unitAt_alloc_ge Fir.Memory.Memory.allocs_alloc Fir.Memory.Memory.length_of_allocs (pin := Fir.Memory.Memory.alloc) (pin := Fir.Memory.Memory.unitAt) (pin := Fir.Memory.Memory.allocs) (fingerprint := "11439987531688671613")
*Theorems: an allocation adds a block after the others.* Let $`M` be a
{ref "The-fir-specification--Memory--The-memory-model"}[memory], and
$`M'` the memory after an allocation of $`n` units, of kind $`k` and
alignment $`a`, in $`M`.

* Each unit of each allocation that $`M` has, $`M'` has unchanged.
* A unit of an allocation past those of $`M` depends only on how many
  allocations $`M` has: two memories with as many allocations give it the
  same value after the same allocation.
* The allocations of $`M'`, each with its kind, alignment, units and
  liveness, are those of $`M` followed by the new one: kind $`k`,
  alignment $`a`, $`n` units, live.
* Two memories with the same allocations have as many blocks.
:::

:::readable Fir.alloc_noUB Fir.alloc_hasOutcome Fir.alloc_finitelyMany (pin := Fir.NoUB) (pin := Fir.HasOutcome) (pin := Fir.FinitelyMany) (pin := Fir.Memory.Memories.alloc) (fingerprint := "6401678105068247993")
*Theorems: an allocation has one outcome.* For every memory $`x`, kind
$`k`, size $`n` and alignment $`a`, the
{ref "The-fir-specification--Memory--The-memory-effect"}[memory effect]'s
allocation in the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer]
never ends in UB, and from any memories $`S` it has exactly one outcome:
the pointer to the new allocation of $`x`, with $`S` and that allocation,
as the
{ref "The-fir-specification--Memory--The-memories-of-a-run"}[memories of a run]
allocate. So it
{ref "The-fir-specification--Memory--Totality-with-memory"}[always has an outcome],
and has
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many].
:::

:::readable Fir.alloc_writesNot (pin := Fir.WritesNot) (fingerprint := "9242305017515739879")
*Theorem: an allocation writes no unit of any memory.* For every memory
$`y`, an allocation in $`x` meets the
{ref "The-fir-specification--Memory--Memory-obligations"}[obligation]
that it writes no unit of $`y`: the units of $`y` before it are a prefix
of the units after it. In $`x` the new allocation's units, all poison,
follow those of the allocations that were there, and every other memory
is unchanged.
:::

:::readable Fir.framesOf_alloc_ne Fir.alloc_allocatesNot (pin := Fir.AllocatesNot) (pin := Fir.Memory.Memories.framesOf) (fingerprint := "14430351169111757673")
*Theorems: an allocation in $`x` allocates in no other memory.* For every
memory $`y \ne x`, after an allocation in $`x`, the frames list the same
stack allocations of $`y`: a stack allocation records its block of $`x`
in the innermost frame, and an allocation of another kind changes no
frame. So an allocation in $`x` meets the
{ref "The-fir-specification--Memory--Memory-obligations"}[obligation]
that it allocates in no memory $`y \ne x`: $`y` keeps its allocations and
the frames its stack allocations.
:::

:::readable Fir.alloc_readsNot (pin := Fir.ReadsNot) (pin := Fir.ReadsNot.Match) (fingerprint := "10195132751089513318")
*Theorem: an allocation reads no memory.* For every memory $`y`, an
allocation meets the
{ref "The-fir-specification--Memory--Memory-obligations"}[obligation]
that it does not read $`y`. Run from memories $`S`, and from $`S` with
$`y` replaced by a memory $`m` of the same allocations, it gives:

* the same pointer, since $`m` has as many blocks as $`S`'s memory $`y`;
* memories that agree off $`y`: the same frames, and every other memory
  the same;
* in $`y`, the same allocations, and each unit either the same in both, as
  the units of a new allocation in $`y` are, or as each run had it before.
:::

:::readable Fir.alloc_refines (pin := Fir.StateRefinedBy) (fingerprint := "18290811390418634203")
*Theorem: an allocation is monotone.* From memories $`S'` that
{ref "The-fir-specification--Memory--Refining-memories"}[refine] $`S`, an
allocation in $`x` gives the same pointer as from $`S`, and memories that
refine those it gives from $`S`. So it is
{ref "The-fir-specification--Memory--Monotonicity-with-memory"}[monotone with memory],
with equal results.
:::
