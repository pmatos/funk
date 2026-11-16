import VersoManual
import Fir.Gpu.WorkGroup
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on work-group allocation, which renders
`Fir.Gpu.WorkGroup` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Work-group allocation: readable blocks" =>

:::moduleDocs (fingerprint := "2251322982091883283")
:::

:::readable Fir.Gpu.Op.memCases Fir.Gpu.allocResult Fir.Gpu.allocAlloc Fir.Gpu.alloc_denote (fingerprint := "3215944786657077571")
*Lemmas: the two kinds of op, and an allocation's run.* A property holds of
every op of `gpu` when it holds of each question and of each allocation. In
the state layer over the set monad, $`\mathsf{alloc}_n~t~c~a` runs as its
allocation in the memory $`\rho(n)`, of the kind $`\mathsf{global}`, with
the pointer it gives as its one result.
:::

:::readable Fir.Gpu.Op.alloc_neverUB Fir.Gpu.Op.alloc_makesNoPoison Fir.Gpu.Op.alloc_writesNot Fir.Gpu.Op.alloc_readsNot Fir.Gpu.Op.alloc_allocatesNot (fingerprint := "9053582269106366143")
*Theorems: an allocation's effects are sound.* At every layout and naming
of `gpu`'s memories, an allocation never ends in UB, gives a pointer, never
poison, writes no unit of any memory, reads none, and allocates in no
memory but $`\rho(n)`, the one it declares.
:::

:::readable Fir.Gpu.Op.alloc_memTotal Fir.Gpu.Op.alloc_memMonotone Fir.Gpu.Op.alloc_memPropagates Fir.Gpu.Op.alloc_memReturnsOnDefined Fir.Gpu.Op.alloc_finitelyMany (fingerprint := "8909698007378109209")
*Theorems: an allocation meets the obligations with memory.* An allocation
has an outcome from any memories. From memories that refine others, it
allocates at the same place, so it gives the same pointer and memories that
refine the others'. It has no operands, so it propagates poison with
memory, and it gives a result from memories inside a call. It has one
outcome from any memories.
:::

:::readable Fir.Gpu.lawfulDialectEffects (fingerprint := "8033647288015854687")
*Theorem: the effect set of `gpu` is sound.* At every work-item, a
question, which declares the empty set, is tied, never ends in UB, makes no
poison on operands with no poison, and, wherever a run names its memories,
writes, reads and allocates in no memory; an allocation does the same,
except that it allocates in the memory it declares; and no op is a
terminator. So the
dialect's declaration of its effects is proved.
:::

:::readable Fir.Gpu.lawfulTotal Fir.Gpu.Op.memMonotone Fir.Gpu.lawfulMonotone Fir.Gpu.lawfulMemPoison (fingerprint := "4225779268134531533")
*Theorems: `gpu` is lawful with memory.* At every work-item, `gpu` is lawful
in its totality, its monotonicity and its poison with memory: a question by
its tie and what it meets in the set monad, and an allocation by its own
rule. Each op is monotone with memory at every width, valid or not, and a
poison value of a core type is refined by every value of its type.
:::
