import VersoManual
import Fir.Execution.MemoryFromAddrLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on turning integers into pointers in the
state layer, which renders `Fir.Execution.MemoryFromAddrLaws`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Turning integers into pointers in the state layer: readable blocks" =>

:::moduleDocs (fingerprint := "9309025559490801763")
:::

:::readable Fir.RebuildsNot (pin := Fir.Memory.Memories) (fingerprint := "13186335698839882115")
*Definition: counts no rebuild.* A computation $`c` of the state layer over
the set monad counts no rebuild when, on each path that ends, from $`S` to
$`S'`, the count of integers turned back into pointers is the same in
$`S'` as in $`S`.
:::

:::readable Fir.rebuildsNot_lift Fir.RebuildsNot.map Fir.RebuildsNot.bind (fingerprint := "6310577601562523244")
*Theorems: building computations that count no rebuild.* A computation
with no memory counts none, and mapping the results of one that counts
none, or sequencing two that count none, counts none.
:::

:::readable Fir.fromAddr_apply Fir.fromAddr_keeps Fir.fromAddr_counts (pin := Fir.instMonadMemoryStateT) (pin := Fir.Memory.Memories.fromAddr) (fingerprint := "15734745923515872297")
*Theorems: how turning an integer into a pointer ends.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad, the
{ref "The-fir-specification--Memory--The-memory-effect"}[memory effect]'s
turning of $`i` of the memory $`x` back into a pointer ends from the
memories $`S` in one way: with the pointer and memories that
{ref "The-fir-specification--Memory--Address-resolvers"}[turning it back]
gives. Those memories have every memory and the frames of $`S`, and count
one more call.
:::

:::readable Fir.fromAddr_hasOutcome Fir.fromAddr_finitelyMany Fir.fromAddr_noUB (pin := Fir.HasOutcome) (pin := Fir.FinitelyMany) (pin := Fir.NoUB) (fingerprint := "7379676401177828433")
*Theorems: one outcome, never UB.* From any memories it has an outcome,
so it {ref "The-fir-specification--Memory--Totality-with-memory"}[always has an outcome],
it has one, so
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many],
and it never ends in UB.
:::

:::readable Fir.fromAddr_writesNot Fir.fromAddr_allocatesNot Fir.fromAddr_exposesNot (pin := Fir.WritesNot) (pin := Fir.AllocatesNot) (pin := Fir.ExposesNot) (fingerprint := "756414423687342611")
*Theorems: no memory changes.* For every memory $`y`, $`x` included, it
meets the
{ref "The-fir-specification--Memory--Memory-obligations"}[obligations]
that it writes no unit of $`y` and neither allocates nor frees in $`y`,
and it exposes nothing in $`y`.
:::

:::readable Fir.fromAddr_readsNot_ne (pin := Fir.ReadsNot) (fingerprint := "7045987943169629677")
*Theorem: it reads no other memory.* For every memory $`y \ne x`, it meets
the {ref "The-fir-specification--Memory--Memory-obligations"}[obligation]
that it does not read $`y`: replacing $`y` changes neither the pointer nor
the count. It reads its own memory: the allocation it picks depends on the
addresses and liveness there.
:::

:::readable Fir.fromAddr_refines (pin := Fir.StateRefinedBy) (fingerprint := "871202169560964149")
*Theorem: turning an integer into a pointer is monotone.* From memories
that refine others, it gives the same pointer and memories that refine
the others'.
:::

:::readable Fir.alloc_rebuildsNot Fir.free_rebuildsNot Fir.load_rebuildsNot Fir.store_rebuildsNot Fir.expose_rebuildsNot (fingerprint := "4730638851404470219")
*Theorems: the other operations count no rebuild.* Allocating, freeing,
loading, storing and exposing count no rebuild: only turning an integer
back into a pointer changes the count.
:::
