import VersoManual
import Fir.Memory.Refine
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on refining memories, which renders
`Fir.Memory.Refine` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Refining memories: readable blocks" =>

:::moduleDocs (fingerprint := "880320936606524875")
:::

:::readable Fir.List.IsRefinedBy.length_eq Fir.List.isRefinedBy_refl Fir.List.IsRefinedBy.append Fir.List.IsRefinedBy.drop Fir.List.IsRefinedBy.take Fir.List.IsRefinedBy.getElem? Fir.List.IsRefinedBy.set Fir.List.IsRefinedBy.modify (pin := Fir.List.IsRefinedBy) (fingerprint := "2883547409260904451")
*Theorems: lists that refine element by element.* A list
$`l'` refines $`l` when they have the same length and each element of
$`l'` refines the element of $`l` at the same index. Then:

* $`|l| = |l'|`, and a list refines itself when each element does;
* appending, dropping the first $`n` elements and taking the first $`n`
  keep refinement: $`l \mathbin{+\!\!+} m \sqsubseteq l' \mathbin{+\!\!+} m'`,
  $`\mathrm{drop}_n(l) \sqsubseteq \mathrm{drop}_n(l')` and
  $`\mathrm{take}_n(l) \sqsubseteq \mathrm{take}_n(l')`;
* at each index $`i`, both lists have no element, or elements $`a` and
  $`a'` with $`a \sqsubseteq a'`;
* replacing the elements at $`i` by $`a \sqsubseteq a'` keeps refinement,
  and so does changing them by a map $`g` that keeps refinement.
:::

:::readable Fir.Memory.MemUnit.IsRefinedBy Fir.Memory.Block.IsRefinedBy Fir.Memory.Memory.IsRefinedBy (fingerprint := "10750520556276307539")
*Definitions: refining units, blocks and memories.* A unit is refined by
itself, and a poison unit by any unit:

$$`\mathsf{poison} \sqsubseteq v \qquad \mathsf{bits}(b) \sqsubseteq v \iff v = \mathsf{bits}(b) \qquad \mathsf{frag}(p, i) \sqsubseteq v \iff v = \mathsf{frag}(p, i)`

So a fragment of a pointer keeps its pointer, and its provenance, in every
memory that refines it, and units of bits keep their bits. A block $`b'`
refines $`b` when it has the same kind and the same liveness, and its
units refine the units of $`b` one by one. A memory refines another when
its blocks refine the other's one by one, in the order they were made: both
have the same allocations, each with its kind, size and liveness.
:::

:::readable Fir.Memory.MemUnit.isRefinedBy_refl Fir.Memory.MemUnit.isRefinedBy_trans Fir.Memory.Block.isRefinedBy_refl Fir.Memory.Block.isRefinedBy_trans Fir.Memory.Memory.isRefinedBy_refl Fir.Memory.Memory.isRefinedBy_trans (fingerprint := "5718639929467021518")
*Theorems: refinement of units, blocks and memories is a preorder.* Each
is reflexive and transitive: a poison unit refined by a unit refined by a
third is refined by the third, and a unit of bits or a fragment is refined
only by itself.
:::

:::readable Fir.Memory.Block.IsRefinedBy.kill Fir.Memory.Memory.IsRefinedBy.free Fir.Memory.Memory.IsRefinedBy.alloc (pin := Fir.Memory.Memory.alloc) (pin := Fir.Memory.Memory.free) (fingerprint := "16019051067054613619")
*Theorems: allocating and freeing keep refinement.* Let $`M \sqsubseteq M'`.
Freeing a block keeps refinement, and so does freeing the allocation $`a`
in both. Allocating $`n` units of kind $`k` in both gives the same pointer,
$`(|M|, 0) = (|M'|, 0)`, since both have as many allocations, and memories
$`M \sqsubseteq M'` again: the new block holds $`n` poisons in both.
:::

:::readable Fir.Memory.Memory.IsRefinedBy.locate Fir.Memory.Memory.IsRefinedBy.load Fir.Memory.Memory.IsRefinedBy.store (pin := Fir.Memory.Memory.locate) (pin := Fir.Memory.Memory.load) (pin := Fir.Memory.Memory.store) (fingerprint := "10007343810621408188")
*Theorems: accesses to memories that refine others.* Let $`M \sqsubseteq M'`.
An access of $`n` units through the pointer $`p` lands, in both, at the
same fault, or in the same allocation at the same offset, in blocks
$`b \sqsubseteq b'`: whether it faults depends only on the allocations,
which are the same. So:

* a load through $`p` faults with the same fault in both, or loads units
  $`u^*` from $`M` and $`u'^*` from $`M'` with $`u^* \sqsubseteq u'^*`;
* a store through $`p` of $`u^*` to $`M` and of $`u'^*` to $`M'`, with
  $`u^* \sqsubseteq u'^*`, faults with the same fault in both, or gives
  memories $`N \sqsubseteq N'`.
:::

:::readable Fir.Memory.Memories.IsRefinedBy Fir.Memory.Memories.isRefinedBy_refl Fir.Memory.Memories.isRefinedBy_trans (fingerprint := "1770885520396180827")
*Definition: refining the memories of a run.* The memories $`S'` of a
run refine $`S` when they have the same frames, and the memory of each
name in $`S'` refines the memory of that name in $`S`:

$$`S \sqsubseteq S' \iff \mathit{frames}(S) = \mathit{frames}(S') \land \forall x.\ \mathit{mem}_S(x) \sqsubseteq \mathit{mem}_{S'}(x)`

It is reflexive and transitive.
:::

:::readable Fir.Memory.Memories.IsRefinedBy.enter Fir.Memory.Memories.IsRefinedBy.set Fir.Memory.Memories.IsRefinedBy.free Fir.Memory.Memories.IsRefinedBy.freeAll Fir.Memory.Memories.IsRefinedBy.exit Fir.Memory.Memories.IsRefinedBy.record (pin := Fir.Memory.Memories.exit) (fingerprint := "18126530047808467220")
*Theorems: frames keep refinement.* Let $`S \sqsubseteq S'`. Entering a
call keeps refinement. Replacing the memory $`x` by $`m` in $`S` and by
$`m'` in $`S'`, with $`m \sqsubseteq m'`, keeps it, and so does freeing an
allocation, or each allocation of a list, in both. Recording a stack
allocation in the innermost frame keeps it. Leaving a call keeps it: both
have the same frames, so both free the allocations of the same innermost
frame.
:::

:::readable Fir.Memory.Memories.IsRefinedBy.alloc Fir.Memory.Memories.IsRefinedBy.load Fir.Memory.Memories.IsRefinedBy.store (fingerprint := "14868621672713175721")
*Theorems: the memory model's operations keep refinement.* Let
$`S \sqsubseteq S'`. Allocating in the memory $`x` of both gives the same
pointer and memories that refine each other; a stack allocation is recorded
in the same frame of both. A load from $`x` through a pointer faults for
the same reason in both, or loads units of which $`S'`'s refine $`S`'s. A
store to $`x` of units that refine others faults for the same reason in
both, or gives memories that refine each other.
:::
