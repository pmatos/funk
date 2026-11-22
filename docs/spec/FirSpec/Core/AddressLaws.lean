import VersoManual
import Fir.Core.AddressLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core dialect's addresses and declared allocations, which
renders `Fir.Core.AddressLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The core dialect's addresses and declared allocations: readable blocks" =>

:::moduleDocs (fingerprint := "16920949359223651501")
:::

:::readable Fir.Core.alloca_keepsAddrs Fir.Core.load_keepsAddrs Fir.Core.store_keepsAddrs Fir.Core.loadPtr_keepsAddrs Fir.Core.storePtr_keepsAddrs Fir.Core.loadFloat_keepsAddrs Fir.Core.storeFloat_keepsAddrs Fir.Core.fieldAddr_keepsAddrs Fir.Core.globalAddr_keepsAddrs Fir.Core.memCopy_keepsAddrs Fir.Core.memSet_keepsAddrs (pin := Fir.KeepsAddrs) (fingerprint := "738361215376009839")
*Theorems: the ops that touch memory keep every address.*
$`\mathsf{alloca}`, the loads and stores of an integer, a pointer and a
float, $`\mathsf{fieldaddr}`, $`\mathsf{globaladdr}`, $`\mathsf{memcpy}`,
$`\mathsf{memmove}` and $`\mathsf{memset}` keep the addresses and the count of every memory: each
runs allocations, loads, stores and choices of bits, which keep them, or
keeps the memories.
:::

:::readable Fir.Core.lawfulDialectAddresses (pin := Fir.LawfulDialectAddresses) (pin := Fir.Core.Op.effects) (fingerprint := "5796012008543201210")
*Theorem: the core's declarations cover addresses.* Every core op that
does not declare an allocation in a memory gives no address and counts no
rebuild there: each tied op keeps the memories, each op above keeps every
address and count, $`\mathsf{ptr\_expose}` gives an address only in the
memory where it declares an allocation, and $`\mathsf{ptr\_from\_int}`
counts a call only there.
:::
