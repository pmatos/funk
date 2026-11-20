import VersoManual
import Fir.Execution.MemoryStoreLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on stores in the state layer, which
renders `Fir.Execution.MemoryStoreLaws` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Stores in the state layer: readable blocks" =>

:::moduleDocs (fingerprint := "11939021943992604842")
:::

:::readable Fir.Memory.Memory.unitAt_eq Fir.Memory.Memory.shape_getElem? Fir.Memory.Memory.locate_allocs (pin := Fir.Memory.Memory.unitAt) (pin := Fir.Memory.Memory.allocs) (pin := Fir.Memory.Memory.locate) (fingerprint := "9578872755073861021")
*Theorems: memories of the same allocations.* The unit at offset $`i` of
the allocation $`a` is the $`i`th unit of the $`a`th block, when both
exist. Two memories of the same
{ref "The-fir-specification--Memory--Memory-obligations"}[allocations]
have, at each id, blocks of the same shape, or no block in both, so an
access lands in both at the same allocation and offset, or faults in both
for the same reason.
:::

:::readable Fir.Memory.Block.write_getElem? Fir.Memory.Memory.allocs_store (fingerprint := "16472162406053145901")
*Theorems: what a write holds.* After writing $`\vec{y}` at offset $`o` of
a block, with $`o + |\vec{y}|` at most its size, its unit at $`i` is
$`\vec{y}[i - o]` when $`o \le i < o + |\vec{y}|`, and the unit it held
at $`i` otherwise. A store keeps a memory's allocations.
:::

:::readable Fir.Memory.Memory.storeAligned_allocs (fingerprint := "12621097333191375768")
*Theorem: a store to memories of the same allocations.* An aligned store
of $`\vec{y}` through $`p` to two memories of the same allocations faults
for the same reason in both, misaligned included, or lands in both in the
same allocation $`a` at the same offset $`o`, and writes $`\vec{y}` at
$`o` of the block of $`a` in each.
:::

:::readable Fir.store_apply Fir.store_ok (pin := Fir.instMonadMemoryStateT) (pin := Fir.Memory.Memories.store) (fingerprint := "12479088072758132017")
*Theorems: how a store ends.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad, the
{ref "The-fir-specification--Memory--The-memory-effect"}[memory effect]'s
store of $`\vec{y}` to the memory $`x` through $`p`, aligned to $`\alpha`
units, ends from the memories $`S` in one of two ways: with the memories
that the aligned store gives, or in UB, for the reason of its fault. The
memories it gives are $`S` with its memory $`x` replaced by one of the
same allocations.
:::

:::readable Fir.store_hasOutcome Fir.store_finitelyMany (pin := Fir.HasOutcome) (pin := Fir.FinitelyMany) (fingerprint := "1395433261851616631")
*Theorems: a store has one outcome.* From any memories a store has an
outcome, so it
{ref "The-fir-specification--Memory--Totality-with-memory"}[always has an outcome],
and at most one that ends, so it has
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many].
:::

:::readable Fir.store_writesNot Fir.store_allocatesNot (pin := Fir.WritesNot) (pin := Fir.AllocatesNot) (fingerprint := "3270893543825609799")
*Theorems: a store writes only its own memory.* For every memory
$`y \ne x`, a store to $`x` meets the
{ref "The-fir-specification--Memory--Memory-obligations"}[obligation]
that it writes no unit of $`y`: $`y` is unchanged. For every memory $`y`,
$`x` included, it neither allocates nor frees in $`y`: a store keeps the
kind, alignment, size and liveness of every allocation, and the frames.
:::

:::readable Fir.store_readsNot_ne Fir.store_readsNot_self Fir.store_readsNot (pin := Fir.ReadsNot) (pin := Fir.ReadsNot.Match) (fingerprint := "9265379715884538705")
*Theorems: a store reads no memory.* For every memory $`y`, a store to
$`x` meets the
{ref "The-fir-specification--Memory--Memory-obligations"}[obligation]
that it does not read $`y`. Run from memories $`S`, and from $`S` with
$`y` replaced by a memory $`m` of the same allocations:

* when $`y \ne x`, it faults for the same reason in both, or writes the
  same memory $`x` in both, and the memories agree off $`y`, whose units
  are those each run had;
* when $`y = x`, its own memory, it faults for the same reason in both,
  since whether a store faults, misaligned included, depends only on the
  allocations; or it writes the same units at the same place of each, and
  every unit of $`x` is the same in both, where it wrote, or as each run
  had it, elsewhere.

So a store declares a write and no read.
:::

:::readable Fir.store_refines (pin := Fir.StateRefinedBy) (fingerprint := "13366743035424057118")
*Theorem: a store is monotone.* To memories $`S'` that
{ref "The-fir-specification--Memory--Refining-memories"}[refine] $`S`, a
store of units $`\vec{y}'` that refine $`\vec{y}` faults for the same
reason as the store of $`\vec{y}` to $`S`, or gives memories that refine
those it gives from $`S`. So it is
{ref "The-fir-specification--Memory--Monotonicity-with-memory"}[monotone with memory].
:::
