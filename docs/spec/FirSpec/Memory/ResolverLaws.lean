import VersoManual
import Fir.Memory.ResolverLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on address resolver laws, which renders
`Fir.Memory.ResolverLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Address resolver laws: readable blocks" =>

:::moduleDocs (fingerprint := "2564905609020490607")
:::

:::readable Fir.Memory.Memory.lt_of_holds Fir.Memory.Memory.holds_iff (pin := Fir.Memory.Memory.holds) (fingerprint := "8474854142891744067")
*Theorems: holding an address.* An allocation that holds an address is
one of the memory. The allocation $`a` holds $`z` exactly when
$`M[a] = (k, \alpha, \vec{x}, \top, y)` with
$`y \le z \le y + |\vec{x}|`.
:::

:::readable Fir.Memory.Memory.pick_holds Fir.Memory.Memory.pick_eq_none Fir.Memory.Memory.resolve_holds Fir.Memory.Memory.resolve_eq_none Fir.Memory.Memory.resolve_of_holds (pin := Fir.Memory.Memory.pick) (pin := Fir.Memory.Memory.resolve) (fingerprint := "6575618705645188425")
*Theorems: the allocation picked holds the address.* The memory model's
pick holds the address, and it picks none exactly when no allocation
holds it. So whatever the proposal, the allocation an address resolves to
holds it; it resolves to none exactly when no allocation holds it; and an
allocation that holds it is the one it resolves to when it is proposed.
:::

:::readable Fir.Memory.Memory.IsRefinedBy.holds Fir.Memory.Memory.IsRefinedBy.resolve Fir.Memory.Memory.IsRefinedBy.rebuild (fingerprint := "901686470942625601")
*Theorems: refinement keeps the allocation picked.* Memories that refine
each other hold the same addresses, resolve an address to the same
allocation on the same proposal, and rebuild the same pointer.
:::

:::readable Fir.Memory.Memories.fromAddr_mem Fir.Memory.Memories.fromAddr_frames Fir.Memory.Memories.fromAddr_rebuilds_self Fir.Memory.Memories.fromAddr_rebuilds_ne Fir.Memory.Memories.fromAddr_prov (pin := Fir.Memory.Memories.fromAddr) (fingerprint := "963373018726342531")
*Theorems: what turning an integer into a pointer changes.* It keeps every
memory and the frames, and counts one more call in its own memory, and
none in any other. The pointer has the
provenance of an allocation that holds the address, or none, and then no
allocation holds it.
:::

:::readable Fir.Memory.Memories.fromAddr_of_holds Fir.Memory.Memories.fromAddr_transfer (fingerprint := "6911018940815718850")
*Theorems: every allocation that holds the address.* At each call, every
allocation $`a` with the address $`y` that holds the address $`z` is the
one picked under the resolver that proposes $`a`, which gives
$`(a, z - y)`. So the union over resolvers holds every choice at each call.
Two memories of a run with the same memory $`x` and the same count of
$`x` give the same pointer.
:::

:::readable Fir.Memory.Memories.IsRefinedBy.fromAddr (fingerprint := "9142005874307699130")
*Theorem: turning an integer into a pointer keeps refinement.* Under the
same resolver, in memories $`S \sqsubseteq S'`, it gives the same pointer
in both, and memories that refine each other.
:::

:::readable Fir.Memory.Memories.fromAddr_expose (fingerprint := "12728293031096875428")
*Theorem: a round trip.* When exposing $`(a, o)` gives the integer $`v`,
and after it $`a` has the address $`y`, with $`0 \le o` and
$`y + o < 2^P`, and $`a` holds $`v`, then turning $`v` back under the
resolver that proposes $`a` gives $`(a, o)` again.
:::
