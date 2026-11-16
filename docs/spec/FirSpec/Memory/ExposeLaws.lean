import VersoManual
import Fir.Memory.ExposeLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on exposure laws, which renders
`Fir.Memory.ExposeLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Exposure laws: readable blocks" =>

:::moduleDocs (fingerprint := "1194117721472522362")
:::

:::readable Fir.Memory.Block.giveAddr_shape Fir.Memory.Block.giveAddr_units Fir.Memory.Block.giveAddr_live Fir.Memory.Block.giveAddr_write (pin := Fir.Memory.Block.giveAddr) (fingerprint := "9446545998985700524")
*Theorems: an address changes no block's contents.* Giving a block an
address keeps its shape, its units and its liveness, and writing to it
then is giving the address to the block written.
:::

:::readable Fir.Memory.Memory.expose_getElem? Fir.Memory.Memory.expose_shapes Fir.Memory.Memory.expose_contents (pin := Fir.Memory.Memory.expose) (fingerprint := "16175337384227445494")
*Theorems: what exposing changes.* After exposing $`a` at $`z`, the
block $`a` is $`\mathrm{give}_z(M[a])` and every other block is as it
was. So every block keeps its shape and its units.
:::

:::readable Fir.Memory.Memory.addrOf_expose_of_none Fir.Memory.Memory.addrOf_expose_of_some Fir.Memory.Memory.addrOf_expose_ne (pin := Fir.Memory.Memory.addrOf) (fingerprint := "18153239210037965542")
*Theorems: the addresses after exposing.* Exposing an allocation of $`M`
with no address at $`z` gives it the address $`z`. One that has the
address $`y` keeps $`y`. Every other allocation keeps its address.
:::

:::readable Fir.Memory.Memory.locate_expose Fir.Memory.Memory.load_expose Fir.Memory.Memory.aligned_expose Fir.Memory.Memory.loadAligned_expose Fir.Memory.Memory.store_expose Fir.Memory.Memory.storeAligned_expose (fingerprint := "4500559863779304412")
*Theorems: exposing changes no access.* An access to an exposed memory
lands where it landed, in the block given the address, or faults for the
same reason. A load, aligned or not, gives what it gave, whether an
access is aligned is the same, and a store, aligned or not, faults for the
same reason or gives the memory it gave, exposed:

$$`\mathrm{store}(M[a := \mathrm{give}_z], p, \vec{y}) = \mathrm{store}(M, p, \vec{y})[a := \mathrm{give}_z]`
:::

:::readable Fir.Memory.Memory.addrOf_alloc_new Fir.Memory.Memory.addrOf_alloc_lt Fir.Memory.Memory.addrOf_free Fir.Memory.Memory.addrOf_store (fingerprint := "10243060688549114162")
*Theorems: the other operations keep addresses.* A new allocation has no
address. Allocating, freeing and storing keep the address of every
allocation, freed or live.
:::

:::readable Fir.Memory.Block.IsRefinedBy.giveAddr Fir.Memory.Memory.IsRefinedBy.expose (fingerprint := "12501599686268958616")
*Theorems: exposing keeps refinement.* Giving the same address to blocks
$`b \sqsubseteq b'` gives blocks that refine each other, since both have
the same address before. So exposing the same allocation at the same
address in $`M \sqsubseteq M'` gives memories that refine each other.
:::

:::readable Fir.Memory.Block.IsRefinedBy.leavesRoom Fir.Memory.roomFrom_isRefinedBy Fir.Memory.Memory.IsRefinedBy.addrOf Fir.Memory.Memory.IsRefinedBy.fits Fir.Memory.Memory.bumpFrom_isRefinedBy Fir.Memory.Memory.lowestFrom_isRefinedBy Fir.Memory.Memory.IsRefinedBy.lowestFit Fir.Memory.Memory.IsRefinedBy.canonical (fingerprint := "1660268409456979510")
*Theorems: refined memories agree on addresses.* Blocks that refine each
other have the same liveness, size and address, so they leave room for
the same addresses. In $`M \sqsubseteq M'` every allocation has the same
address, the same addresses fit it, its canonical address is the same,
the lowest address that fits it is the same, and the canonical layout
gives it the same address.
:::
