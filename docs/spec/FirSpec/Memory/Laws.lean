import VersoManual
import Fir.Memory.Laws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on memory laws, which renders
`Fir.Memory.Laws` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Memory laws: readable blocks" =>

:::moduleDocs (fingerprint := "3841386511490742844")
:::

:::readable Fir.Memory.Block.write_length (fingerprint := "6572027941022401979")
*Theorem: a write keeps a block's size.* If $`o + |\vec{y}| \le |\vec{x}|`,
then writing $`\vec{y}` at $`o` leaves the block with $`|\vec{x}|` units.
:::

:::readable Fir.Memory.Block.read_write_same (fingerprint := "17083795552365235224")
*Theorem: a read gives back what a write wrote.* If
$`o + |\vec{y}| \le |\vec{x}|`, then reading $`|\vec{y}|` units at $`o`
after writing $`\vec{y}` there gives $`\vec{y}`.
:::

:::readable Fir.Memory.Block.read_write_disjoint (fingerprint := "4078727027548765309")
*Theorem: a write leaves the units it does not touch.* If
$`o + |\vec{y}| \le |\vec{x}|`, and the $`n` units from $`o'` lie wholly
before or wholly after the units from $`o` to $`o + |\vec{y}|`, then
reading them after writing $`\vec{y}` at $`o` gives what it gave before.
:::

:::readable Fir.Memory.Memory.locate_eq_ok (fingerprint := "16502042792774658033")
*Theorem: when an access succeeds.* An access of $`n` units through
$`(a^?, o)` lands in the block $`b` of the allocation $`a`, at offset $`o`,
exactly when the pointer has provenance for $`a`, $`M[a] = b`, $`b` is
live, $`0 \le o` and $`o + n \le |b|`.
:::

:::readable Fir.Memory.Memory.locate_none Fir.Memory.Memory.locate_unknown (fingerprint := "13857559264405580733")
*Theorem: an access without provenance is UB.* An access through a pointer
with no provenance faults with $`\mathsf{noProvenance}`, and so does one
through a pointer whose allocation the memory does not have.
:::

:::readable Fir.Memory.Memory.locate_freed (fingerprint := "17273021243933917122")
*Theorem: an access to a freed allocation is UB.* If $`M[a]` is not live,
every access through a pointer with provenance for $`a` faults with
$`\mathsf{freed}`.
:::

:::readable Fir.Memory.Memory.locate_outOfBounds (fingerprint := "16680091370023247280")
*Theorem: an access out of bounds is UB.* If $`M[a]` is live and the
$`n` units from $`o` are not all inside it, the access of $`n` units
through $`(a, o)` faults with $`\mathsf{outOfBounds}`.
:::

:::readable Fir.Memory.Memory.load_eq_error Fir.Memory.Memory.store_eq_error (fingerprint := "7541163938030258180")
*Theorem: loads and stores fault as their accesses do.* A load of $`n`
units faults exactly when its access of $`n` units does, and a store of
$`\vec{y}` exactly when its access of $`|\vec{y}|` units does, each for the
same reason.
:::

:::readable Fir.Memory.Memory.load_of_locate Fir.Memory.Memory.store_of_locate (fingerprint := "17546964793698600514")
*Theorem: what a successful access does.* When an access lands in the
block $`b` of $`a` at offset $`o`, a load gives $`b`'s units from $`o` on,
and a store of $`\vec{y}` gives $`M` with $`M[a] := b[o := \vec{y}]`.
:::

:::readable Fir.Memory.Memory.store_eq_ok (fingerprint := "93568961109510418")
*Theorem: what a store leaves.* If storing $`\vec{y}` through $`p` gives
$`M'`, then its access landed in some block $`b` of $`a` at $`o`, and
$`M'` is $`M` with $`M[a] := b[o := \vec{y}]`.
:::

:::readable Fir.Memory.Memory.alloc_fst (fingerprint := "17438683236702964508")
*Theorem: the pointer an allocation gives.* Allocating in $`M` gives the
pointer $`(|M|, 0)`: provenance for the new allocation, which no allocation
had before, and its first unit.
:::

:::readable Fir.Memory.Memory.alloc_blocks_lt Fir.Memory.Memory.alloc_blocks_new (fingerprint := "5419404848170668150")
*Theorem: an allocation adds one block and changes none.* After an
allocation of $`n` units of kind $`k`, every allocation $`a < |M|` has the
block it had, and the new allocation $`|M|` has the live block
$`(k, \mathsf{poison}^n, \mathsf{true})`.
:::

:::readable Fir.Memory.Memory.load_alloc (fingerprint := "4352129680637838304")
*Theorem: fresh memory holds poison.* After allocating $`s` units, a load
of $`n` units through $`(|M|, o)`, with $`0 \le o` and $`o + n \le s`,
gives $`\mathsf{poison}^n`.
:::

:::readable Fir.Memory.Memory.store_blocks_ne (fingerprint := "10846841074154781668")
*Theorem: a store changes no other allocation.* If storing through $`p`
gives $`M'`, then $`M'[a] = M[a]` for every allocation $`a` that $`p` has
no provenance for.
:::

:::readable Fir.Memory.Memory.store_shape (fingerprint := "10336796153857920541")
*Theorem: a store keeps every allocation's shape.* If a store gives
$`M'`, then for every $`a`, $`M'[a]` has the kind, size and liveness of
$`M[a]`, and $`M'` has a block for $`a` exactly when $`M` has one.
:::

:::readable Fir.Memory.Memory.locate_store (fingerprint := "7904502745175208077")
*Theorem: a store changes no access's outcome.* If a store gives $`M'`,
then every access in $`M'` lands in the allocation and at the offset where
it landed in $`M`, or faults for the same reason.
:::

:::readable Fir.Memory.Memory.load_store_same (fingerprint := "9240027937220950642")
*Theorem: a load after a store gives what was stored.* If storing
$`\vec{y}` through $`p` gives $`M'`, then loading $`|\vec{y}|` units through
$`p` in $`M'` gives $`\vec{y}`.
:::

:::readable Fir.Memory.Memory.load_store_ne (fingerprint := "14110339019664070808")
*Theorem: a store leaves loads from other allocations.* If storing through
$`p` gives $`M'`, then every load in $`M'` through a pointer whose
provenance differs from $`p`'s gives what it gave in $`M`.
:::

:::readable Fir.Memory.Memory.load_store_disjoint (fingerprint := "3765793166822479529")
*Theorem: a store leaves loads of units it does not touch.* If storing
$`\vec{y}` through $`p = (a, o)` gives $`M'`, then a load of $`n` units
through $`(a, o')`, where $`o' + n \le o` or $`o + |\vec{y}| \le o'`, gives
in $`M'` what it gave in $`M`.
:::

:::readable Fir.Memory.Memory.free_blocks_ne (fingerprint := "2352086048335710784")
*Theorem: a free changes no other allocation.* After freeing $`a`, every
allocation $`a' \ne a` has the block it had.
:::

:::readable Fir.Memory.Memory.locate_free (fingerprint := "6746748068632546069")
*Theorem: after a free, every access is UB.* If $`a < |M|`, then after
freeing $`a`, every access through a pointer with provenance for $`a`
faults with $`\mathsf{freed}`.
:::
