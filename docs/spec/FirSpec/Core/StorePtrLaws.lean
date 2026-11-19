import VersoManual
import Fir.Core.StorePtrLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the pointer store obligations, which
renders `Fir.Core.StorePtrLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Pointer store obligations: readable blocks" =>

:::moduleDocs (fingerprint := "1960113562441878415")
:::

:::readable Fir.Core.storePtrAccess Fir.Core.storePtr_denote Fir.Core.storePtr_ownRuleHas (pin := Fir.Core.storePtrRule) (pin := Fir.Core.memDenoteAt) (pin := Fir.OwnRuleHas) (fingerprint := "3554754592212507456")
*Definitions and theorems: the store of a pointer with memory.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad, at the layout entries $`\ell` and naming $`\rho`, the
meaning of $`\mathsf{store}_N~o~\mathsf{ptr}\langle M \rangle~a` on the
value $`v` and the pointer $`p` is its
{ref "The-fir-specification--Memory--Pointer-load-and-store-rules"}[rule].
So what it runs by its own rule has a property when its rule has it on
every value and pointer.
:::

:::readable Fir.Core.storePtr_writesNot Fir.Core.storePtr_readsNot Fir.Core.storePtr_allocatesNot (pin := Fir.WritesNot) (pin := Fir.ReadsNot) (pin := Fir.AllocatesNot) (fingerprint := "16397300765104006661")
*Theorems: the store of a pointer touches memory only by writing where it
declares.* At every layout $`\ell` and naming $`\rho`, it writes no memory
but $`\rho(N)`, the one its
{ref "The-fir-specification--Execution--Effect-sets"}[effect set],
$`\mathsf{writes}(N)`, names. It reads no memory, $`\rho(N)` included,
and neither allocates nor frees in any. Each follows from the
{ref "The-fir-specification--Memory--Stores-in-the-state-layer"}[store's]
own laws, since the units it writes are a function of its value alone.
:::

:::readable Fir.Core.storePtr_memTotal Fir.Core.storePtr_finitelyMany (pin := Fir.MemTotal) (pin := Fir.FinitelyMany) (fingerprint := "16789302652203864475")
*Theorems: the store of a pointer has an outcome, and at most one that
ends.* From any memories it ends in UB or gives the memories with its
units written: it is
{ref "The-fir-specification--Memory--Totality-with-memory"}[total with memory],
and it has
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many outcomes].
:::

:::readable Fir.Core.storePtr_makesNoPoison (pin := Fir.MakesNoPoison) (fingerprint := "14901249159893415990")
*Theorem: the store of a pointer makes no poison.* It gives no result, so
no result of it is poison, whatever it stores.
:::

:::readable Fir.Core.storePtr_memMonotone (pin := Fir.MemMonotone) (fingerprint := "18237444346312468320")
*Theorem: the store of a pointer is monotone with memory.* A poison
pointer is UB, which every outcome refines. A defined pointer is refined
only by itself, and a value that refines another has an encoding that
{ref "The-fir-specification--Memory--Laws-of-values-in-units"}[refines]
the other's, unit by unit, so to memories that refine others the store
faults for the same reason or gives memories that refine the others'.
:::

:::readable Fir.Core.storePtr_memPropagates Fir.Core.storePtr_memReturnsOnDefined (pin := Fir.MemPropagatesPoison) (pin := Fir.MemReturnsOnDefined) (fingerprint := "11399571801846117305")
*Theorems: the store of a pointer propagates poison with memory, and
returns on defined operands.* It gives no result. On a poison pointer, the
UB it gives from memories $`S` is the UB that a pointer with no
provenance in its place gives, whatever the value. On a poison value and
a defined pointer it is UB only when the store of its poison units
faults, and then a store of a pointer with no provenance in its place, as
many units, faults for the same reason. It returns on defined operands:
a pointer with no provenance, stored to a fresh allocation of its units
at its alignment, in memory $`\rho(N)` of $`\mathsf{Memories.empty}`
entered. So it meets the
{ref "The-fir-specification--Memory--Poison-obligations-with-memory"}[poison obligations with memory].
:::
