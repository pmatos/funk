import VersoManual
import Fir.Core.StoreFloatLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the float store obligations, which
renders `Fir.Core.StoreFloatLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Float store obligations: readable blocks" =>

:::moduleDocs (fingerprint := "11807418051268259110")
:::

:::readable Fir.Core.storeFloat_denote Fir.Core.storeFloatRule_poison Fir.Core.storeFloatRule_value Fir.Core.storeFloat_ownRuleHas (pin := Fir.Core.storeFloatRule) (pin := Fir.Core.storeAccess) (pin := Fir.Core.memDenoteAt) (pin := Fir.OwnRuleHas) (fingerprint := "12086484347473594091")
*Theorems: the store of a float with memory.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad, at the layout entries $`\ell` and naming $`\rho`, the
meaning of $`\mathsf{store}_N~o~\mathsf{float}\langle e,m \rangle~a` on
the value $`v` and the pointer $`p` is its
{ref "The-fir-specification--Memory--Float-load-and-store-rules"}[rule]: UB
on a poison pointer, from any memories, and on a pointer the store of the
encoding of $`v`'s bits as an $`\mathsf{i}W`, $`W = 1 + e + m`, with no
result. So what it runs by its own rule has a property when its rule has
it on every value and pointer.
:::

:::readable Fir.Core.storeFloat_writesNot Fir.Core.storeFloat_readsNot Fir.Core.storeFloat_allocatesNot (pin := Fir.WritesNot) (pin := Fir.ReadsNot) (pin := Fir.AllocatesNot) (fingerprint := "2158650973243288808")
*Theorems: the store of a float touches memory only by writing where it
declares.* At every layout $`\ell` and naming $`\rho`, it writes no memory
but $`\rho(N)`, the one its
{ref "The-fir-specification--Execution--Effect-sets"}[effect set],
$`\mathsf{writes}(N)`, names. It reads no memory, $`\rho(N)` included,
and neither allocates nor frees in any. Each follows from the
{ref "The-fir-specification--Memory--Stores-in-the-state-layer"}[store's]
own laws, since the units it writes are a function of its value alone.
:::

:::readable Fir.Core.storeFloat_memTotal Fir.Core.storeFloat_finitelyMany (pin := Fir.MemTotal) (pin := Fir.FinitelyMany) (fingerprint := "511521990978585944")
*Theorems: the store of a float has an outcome, and at most one that
ends.* From any memories it ends in UB or gives the memories with its
units written: it is
{ref "The-fir-specification--Memory--Totality-with-memory"}[total with memory],
and it has
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many outcomes].
:::

:::readable Fir.Core.storeFloat_makesNoPoison (pin := Fir.MakesNoPoison) (fingerprint := "5133395169964867687")
*Theorem: the store of a float makes no poison.* It gives no result, so no
result of it is poison, whatever it stores.
:::

:::readable Fir.Core.storeFloat_memMonotone (pin := Fir.MemMonotone) (fingerprint := "8741035606187026478")
*Theorem: the store of a float is monotone with memory.* A poison pointer
is UB, which every outcome refines. A defined pointer is refined only by
itself, and a float that refines another has an encoding that
{ref "The-fir-specification--Memory--Laws-of-values-in-units"}[refines]
the other's, unit by unit, so to memories that refine others the store
faults for the same reason or gives memories that refine the others'.
:::

:::readable Fir.Core.storeFloat_memPropagates Fir.Core.storeFloat_memReturnsOnDefined (pin := Fir.MemPropagatesPoison) (pin := Fir.MemReturnsOnDefined) (fingerprint := "5542093834854281161")
*Theorems: the store of a float propagates poison with memory, and
returns on defined operands.* It gives no result. On a poison pointer, the
UB it gives from memories $`S` is the UB that a pointer with no provenance
in its place gives, whatever the value. On a poison float and a defined
pointer it is UB only when the store of its poison units faults, and then
a store of the float whose bits are zero, as many units, faults for the
same reason. It returns on defined operands: the float whose bits are
zero, stored to a fresh allocation of its units at its alignment, in
memory $`\rho(N)` of $`\mathsf{Memories.empty}` entered. So it meets the
{ref "The-fir-specification--Memory--Poison-obligations-with-memory"}[poison obligations with memory].
:::
