import VersoManual
import Fir.Memory.AlignLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on aligned access laws, which renders
`Fir.Memory.AlignLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Aligned access laws: readable blocks" =>

:::moduleDocs (fingerprint := "12590413594868773260")
:::

:::readable Fir.Memory.Memory.aligned_one (pin := Fir.Memory.Memory.aligned) (fingerprint := "17422207254607626637")
*Theorem: every access is aligned to 1.* For every memory $`M` and
pointer $`p`, $`\mathrm{aligned}_M(p, 1)`: 1 divides every alignment and
every offset.
:::

:::readable Fir.Memory.Memory.loadAligned_of_aligned Fir.Memory.Memory.storeAligned_of_aligned Fir.Memory.Memory.loadAligned_one Fir.Memory.Memory.storeAligned_one (pin := Fir.Memory.Memory.loadAligned) (pin := Fir.Memory.Memory.storeAligned) (fingerprint := "17017086476499583596")
*Theorems: an aligned access is the plain one.* When an access through
$`p` aligned to $`\alpha` units is aligned, the aligned load of $`n`
units is the plain load of $`n` units, and the aligned store of
$`\vec{y}` is the plain store of $`\vec{y}`: they succeed, or fault, as
those do. Since every access is aligned to 1, a load or a store aligned
to 1 is the plain one.
:::

:::readable Fir.Memory.Memory.loadAligned_eq_ok Fir.Memory.Memory.storeAligned_eq_ok (fingerprint := "3206784631234904290")
*Theorems: when an aligned access succeeds.* An aligned load gives the
units $`\vec{x}` exactly when the plain load gives $`\vec{x}` and the
access is aligned. An aligned store gives the memory $`M'` exactly when
the plain store gives $`M'` and the access is aligned.
:::

:::readable Fir.Memory.Memory.loadAligned_of_error Fir.Memory.Memory.storeAligned_of_error Fir.Memory.Memory.loadAligned_misaligned Fir.Memory.Memory.storeAligned_misaligned (fingerprint := "5067851333010923815")
*Theorems: how an aligned access faults.* Where the plain load or store
faults, the aligned one faults for the same reason, whatever its
alignment: the faults of the
{ref "The-fir-specification--Memory--The-memory-model"}[model] come
first. Where the plain one succeeds but the access is not aligned, the
aligned one faults as $`\mathsf{misaligned}`.
:::

:::readable Fir.Memory.Memory.aligned_of_shapes Fir.Memory.Memory.aligned_store (pin := Fir.Memory.Block.shape) (fingerprint := "10216916223102833512")
*Theorems: alignment depends on no unit.* Two memories whose blocks have
the same shapes, one by one, agree on whether each access is aligned:
whether it is depends only on the alignment of its block and on its
pointer. A store keeps every block's shape, so after a store every access
is aligned exactly when it was before.
:::

:::readable Fir.Memory.Memory.aligned_alloc (fingerprint := "9396087903521846653")
*Theorem: an access at the start of a new allocation.* After an
allocation of alignment $`\alpha'` in $`M`, an access through the pointer
it gives, at offset 0, aligned to $`\alpha`, is aligned exactly when
$`\alpha \mid \alpha'`.
:::
