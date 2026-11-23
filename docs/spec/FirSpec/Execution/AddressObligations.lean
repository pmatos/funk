import VersoManual
import Fir.Execution.AddressObligations
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on addresses and the declared allocation, which
renders `Fir.Execution.AddressObligations` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Addresses and the declared allocation: readable blocks" =>

:::moduleDocs (fingerprint := "15791714511247236849")
:::

:::readable Fir.KeepsAddrs Fir.keepsAddrs_lift Fir.KeepsAddrs.map Fir.KeepsAddrs.bind Fir.KeepsAddrs.chooseBind (pin := Fir.ExposesNot) (pin := Fir.RebuildsNot) (fingerprint := "16988344933831160477")
*Definition and lemmas: keeping addresses and the count.* A computation
keeps the addresses and the count of the memory $`x` when it gives no
allocation of $`x` an address and counts no integer turned back into a
pointer of $`x`. A computation with no memory keeps them, and mapping the
results, sequencing and a choice of bits keep them.
:::

:::readable Fir.alloc_keepsAddrs Fir.load_keepsAddrs Fir.store_keepsAddrs (pin := Fir.MonadMemory) (fingerprint := "2333023474265235660")
*Lemmas: allocating, loading and storing keep them.* An allocation, a load
and a store keep the addresses and the count of every memory.
:::

:::readable Fir.LawfulDialectAddresses (pin := Fir.OwnRuleHas) (pin := Fir.ExposesNot) (pin := Fir.RebuildsNot) (fingerprint := "1106717029422483670")
*Definition: declarations that cover addresses.* A dialect's allocation
declarations cover addresses and rebuilds when every valid op that runs by
its own rule, a terminator or an op with no callee, wherever a run names
the dialect's memories, gives no allocation of a memory $`x` an address and
counts no integer turned back into a pointer of $`x`, for every $`x` in
which it does not declare an allocation. Exposing counts as allocating in
its memory (the human's ruling of 2026-11-20 on #232, question B), and
so does the count (the human's ruling of 2026-11-21 on #232).
:::

:::readable Fir.OwnRuleHas.addrs Fir.OwnRuleHas.keeps Fir.LawfulDialectAddresses.ofKeeps (fingerprint := "10516353205826156502")
*Lemmas: meeting the obligations.* An op whose own rule keeps the
addresses and the count of $`x` gives no address and counts no rebuild
there, and conversely. A dialect meets both obligations when each valid op
keeps the addresses and the count of each memory where it does not declare
an allocation.
:::
