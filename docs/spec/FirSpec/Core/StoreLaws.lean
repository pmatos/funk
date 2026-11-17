import VersoManual
import Fir.Core.StoreLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the store obligations, which renders
`Fir.Core.StoreLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Store obligations: readable blocks" =>

:::moduleDocs (fingerprint := "17495321334511808242")
:::

:::readable Fir.Memory.Memory.storeAligned_error_length Fir.Memory.Memories.store_error_length (pin := Fir.Memory.Memory.storeAligned) (pin := Fir.Memory.Memories.store) (fingerprint := "9244491371724419118")
*Theorems: a store faults by how many units it writes.* If an aligned store
of the units $`u^*` through $`p`, aligned to $`a`, faults for the reason
$`f`, in one memory or in a memory of a run, then a store of any units
$`u'^*` with as many units as $`u^*` through $`p`, aligned to $`a`, faults
for $`f` too. A store locates its units by their number alone, and its
alignment check reads the allocations, not the units.
:::

:::readable Fir.Core.storeAccess Fir.Core.store_denote Fir.Core.storeRule_poison Fir.Core.storeRule_value Fir.Core.store_ownRuleHas (pin := Fir.Core.storeRule) (pin := Fir.Core.memDenoteAt) (pin := Fir.OwnRuleHas) (fingerprint := "17479065974873850673")
*Definitions and theorems: $`\mathsf{store}` with memory.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad, at the layout entries $`\ell` and naming $`\rho`, the
meaning of $`\mathsf{store}_N~o~W~a` on the operands $`v` and $`p` is its
{ref "The-fir-specification--Memory--Store-rules"}[rule]: on a poison
pointer, UB from any memories and nothing else; on a pointer $`q`, the
{ref "The-fir-specification--Memory--Stores-in-the-state-layer"}[store]
through $`q` of the units of $`v` to $`\rho(N)`, with no result. So what
$`\mathsf{store}` runs by its own rule has a property when its rule has it
on every value and pointer operand.
:::

:::readable Fir.Core.store_writesNot Fir.Core.store_readsNot Fir.Core.store_allocatesNot (pin := Fir.WritesNot) (pin := Fir.ReadsNot) (pin := Fir.AllocatesNot) (fingerprint := "4024226227505133826")
*Theorems: $`\mathsf{store}` touches memory only by writing where it
declares.* At every layout $`\ell` and naming $`\rho`, and for every
memory $`y` of the run, $`\mathsf{store}_N` by its own rule writes no unit
of any memory $`y` that its
{ref "The-fir-specification--Execution--Effect-sets"}[effect set],
$`\mathsf{writes}(N)`, named through $`\rho`, leaves out: every
$`y \ne \rho(N)`. It reads no memory, $`\rho(N)` included, and neither
allocates nor frees in any. On a poison pointer it ends only in UB, for
the same reason from every memories; on a pointer each follows from the
{ref "The-fir-specification--Memory--Stores-in-the-state-layer"}[store's]
own laws, since the units it writes are a function of its value alone.
:::

:::readable Fir.Core.store_memTotal Fir.Core.store_finitelyMany (pin := Fir.MemTotal) (pin := Fir.FinitelyMany) (fingerprint := "12127326507528065956")
*Theorems: $`\mathsf{store}` has an outcome, and at most one that ends.*
From any memories, $`\mathsf{store}` ends in UB or gives the memories with
its units written: it is
{ref "The-fir-specification--Memory--Totality-with-memory"}[total with memory].
It has at most one outcome that ends, so it has
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many outcomes].
:::

:::readable Fir.Core.store_makesNoPoison (pin := Fir.MakesNoPoison) (fingerprint := "16391792131043240424")
*Theorem: $`\mathsf{store}` makes no poison.* It gives no result, so no
result of it is poison, whatever it stores.
:::

:::readable Fir.Core.store_memMonotone (pin := Fir.MemMonotone) (fingerprint := "8037822513278812782")
*Theorem: $`\mathsf{store}` is monotone with memory.* On operands that
refine others, to memories that refine others, $`\mathsf{store}`'s
outcomes refine the other's. A poison pointer is UB, which every outcome
refines. A defined pointer is refined only by itself, and a value that
refines another has an encoding that
{ref "The-fir-specification--Memory--Laws-of-values-in-units"}[refines]
the other's, unit by unit, so the store faults for the same reason or
gives memories that refine the others'.
:::

:::readable Fir.Core.store_memPropagates Fir.Core.store_memReturnsOnDefined (pin := Fir.MemPropagatesPoison) (pin := Fir.MemReturnsOnDefined) (fingerprint := "1966509810676032635")
*Theorems: $`\mathsf{store}` propagates poison with memory, and returns on
defined operands.* It gives no result, so a poison operand gives no poison
result. On a poison pointer, the UB it gives from memories $`S` is the UB
that a pointer with no provenance in its place gives from $`S`, whatever
the value. On a poison value and a defined pointer it is UB only when the
store of its poison units faults, and then a store of the zero of
$`\mathsf{i}W` in its place, as many units, faults for the same reason. It
returns on defined operands from memories inside a call: the zero of
$`\mathsf{i}W`, stored to a fresh allocation of its units at the store's
alignment, in memory $`\rho(N)` of $`\mathsf{Memories.empty}` entered.
So $`\mathsf{store}` meets the
{ref "The-fir-specification--Memory--Poison-obligations-with-memory"}[poison obligations with memory].
:::
