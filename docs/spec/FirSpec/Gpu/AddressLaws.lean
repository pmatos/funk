import VersoManual
import Fir.Gpu.AddressLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on gpu's addresses and declared allocations, which
renders `Fir.Gpu.AddressLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Gpu addresses and declared allocations: readable blocks" =>

:::moduleDocs (fingerprint := "2369309394381797186")
:::

:::readable Fir.Gpu.Op.alloc_keepsAddrs Fir.Gpu.lawfulAddresses Fir.Gpu.coreGpu_lawfulAddresses (pin := Fir.LawfulDialectAddresses) (fingerprint := "1674752865669587683")
*Theorems: `gpu`'s declarations cover addresses.* An allocation of
`gpu.work_group_alloca` keeps every address and count, and a question
keeps the memories, so `gpu`'s declarations cover addresses and rebuilds at
every work-item, and so do those of the sum `CoreGpu`.
:::
