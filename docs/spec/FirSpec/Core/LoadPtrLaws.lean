import VersoManual
import Fir.Core.LoadPtrLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the pointer load obligations, which
renders `Fir.Core.LoadPtrLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Pointer load obligations: readable blocks" =>

:::moduleDocs (fingerprint := "4149560778941201635")
:::

:::readable Fir.Core.loadPtrAccess Fir.Core.loadPtr_denote Fir.Core.loadPtr_ownRuleHas (pin := Fir.Core.loadPtrRule) (pin := Fir.Core.memDenoteAt) (pin := Fir.OwnRuleHas) (fingerprint := "11483236102255436387")
*Definitions and theorems: the load of a pointer with memory.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad, at the layout entries $`\ell` and naming $`\rho`, the
meaning of $`\mathsf{load}_N~o~\mathsf{ptr}\langle M \rangle~a` on the
pointer $`p` is its
{ref "The-fir-specification--Memory--Pointer-load-and-store-rules"}[rule].
So what it runs by its own rule has a property when its rule has it on
every pointer.
:::

:::readable Fir.Core.loadPtr_writesNot Fir.Core.loadPtr_allocatesNot Fir.Core.loadPtr_readsNot (pin := Fir.WritesNot) (pin := Fir.ReadsNot) (pin := Fir.AllocatesNot) (fingerprint := "15595423325696301472")
*Theorems: the load of a pointer touches memory only by reading where it
declares.* At every layout $`\ell` and naming $`\rho`, it writes no unit
of any memory, allocates and frees in none, and reads no memory but
$`\rho(N)`, the one its
{ref "The-fir-specification--Execution--Effect-sets"}[effect set],
$`\mathsf{reads}(N)`, names: never the memory $`M` of the pointer it
loads. Each follows from the
{ref "The-fir-specification--Memory--Loads-in-the-state-layer"}[load's]
own laws.
:::

:::readable Fir.Core.loadPtr_memTotal Fir.Core.loadPtr_finitelyMany (pin := Fir.MemTotal) (pin := Fir.FinitelyMany) (fingerprint := "14054923403509672839")
*Theorems: the load of a pointer has an outcome, and at most one that
ends.* From any memories it ends in UB or gives a value, a pointer or
poison: it is
{ref "The-fir-specification--Memory--Totality-with-memory"}[total with memory],
and it has
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many outcomes].
:::

:::readable Fir.Core.loadPtr_memMonotone (pin := Fir.MemMonotone) (fingerprint := "14549399474543527207")
*Theorem: the load of a pointer is monotone with memory.* A poison
pointer is UB, which every outcome refines. On the same pointer, from
memories that refine others, the load faults for the same reason or loads
units that refine the others', and their decoding as a pointer
{ref "The-fir-specification--Memory--Laws-of-values-in-units"}[refines]
the others' value.
:::

:::readable Fir.Core.loadPtr_memPropagates Fir.Core.loadPtr_memReturnsOnDefined (pin := Fir.MemPropagatesPoison) (pin := Fir.MemReturnsOnDefined) (fingerprint := "6582210912202632347")
*Theorems: the load of a pointer propagates poison with memory, and
returns on defined operands.* A poison pointer gives no result, and the
UB it gives from memories $`S` is the UB of a pointer with no provenance
in its place, from $`S`. From memories inside a call that hold a fresh
allocation of its units at its alignment, the load through the pointer to
it gives the value its poison units decode to. So it meets the
{ref "The-fir-specification--Memory--Poison-obligations-with-memory"}[poison obligations with memory].
:::
