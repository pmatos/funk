import VersoManual
import Fir.Core.LoadFloatLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the float load obligations, which
renders `Fir.Core.LoadFloatLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Float load obligations: readable blocks" =>

:::moduleDocs (fingerprint := "3358301174367549831")
:::

:::readable Fir.Core.loadFloat_denote Fir.Core.loadFloatRule_poison Fir.Core.loadFloatRule_value Fir.Core.loadFloat_ownRuleHas (pin := Fir.Core.loadFloatRule) (pin := Fir.Core.loadAccess) (pin := Fir.Core.memDenoteAt) (pin := Fir.OwnRuleHas) (fingerprint := "13402394669751527305")
*Theorems: the load of a float with memory.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad, at the layout entries $`\ell` and naming $`\rho`, the
meaning of $`\mathsf{load}_N~o~\mathsf{float}\langle e,m \rangle~a` on the
pointer $`p` is its
{ref "The-fir-specification--Memory--Float-load-and-store-rules"}[rule]: UB
on a poison pointer, from any memories, and on a pointer the load of the
units of $`\mathsf{i}W`, $`W = 1 + e + m`, decoded. So what it runs by its
own rule has a property when its rule has it on every pointer.
:::

:::readable Fir.Core.loadFloat_writesNot Fir.Core.loadFloat_allocatesNot Fir.Core.loadFloat_readsNot (pin := Fir.WritesNot) (pin := Fir.ReadsNot) (pin := Fir.AllocatesNot) (fingerprint := "872194356433768512")
*Theorems: the load of a float touches memory only by reading where it
declares.* At every layout $`\ell` and naming $`\rho`, it writes no unit
of any memory, allocates and frees in none, and reads no memory but
$`\rho(N)`, the one its
{ref "The-fir-specification--Execution--Effect-sets"}[effect set],
$`\mathsf{reads}(N)`, names. Each follows from the
{ref "The-fir-specification--Memory--Loads-in-the-state-layer"}[load's]
own laws.
:::

:::readable Fir.Core.loadFloat_memTotal Fir.Core.loadFloat_finitelyMany (pin := Fir.MemTotal) (pin := Fir.FinitelyMany) (fingerprint := "5385834950168520505")
*Theorems: the load of a float has an outcome, and at most one that
ends.* From any memories it ends in UB or gives a value, a float or
poison: it is
{ref "The-fir-specification--Memory--Totality-with-memory"}[total with memory],
and it has
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many outcomes].
:::

:::readable Fir.Core.loadFloat_memMonotone (pin := Fir.MemMonotone) (fingerprint := "5774228941786999919")
*Theorem: the load of a float is monotone with memory.* A poison pointer
is UB, which every outcome refines. On the same pointer, from memories
that refine others, the load faults for the same reason or loads units
that refine the others', and their decoding as the integer of the float's
bits {ref "The-fir-specification--Memory--Laws-of-values-in-units"}[refines]
the others' value.
:::

:::readable Fir.Core.loadFloat_memPropagates Fir.Core.loadFloat_memReturnsOnDefined (pin := Fir.MemPropagatesPoison) (pin := Fir.MemReturnsOnDefined) (fingerprint := "13640110920788482543")
*Theorems: the load of a float propagates poison with memory, and returns
on defined operands.* A poison pointer gives no result, and the UB it
gives from memories $`S` is the UB of a pointer with no provenance in its
place, from $`S`. From memories inside a call that hold a fresh allocation
of its units at its alignment, the load through the pointer to it gives
the value its poison units decode to. So it meets the
{ref "The-fir-specification--Memory--Poison-obligations-with-memory"}[poison obligations with memory].
:::
