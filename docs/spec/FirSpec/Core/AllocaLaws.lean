import VersoManual
import Fir.Core.AllocaLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the stack allocation obligations,
which renders `Fir.Core.AllocaLaws` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Stack allocation obligations: readable blocks" =>

:::moduleDocs (fingerprint := "9883967547700479962")
:::

:::readable Fir.Core.Op.memCases Fir.Core.Op.touchesMemory_false_of_denote (pin := Fir.Core.Op.touchesMemory) (fingerprint := "16621215638438812656")
*Theorems: the core ops, split by memory.* A property holds of every core
op when it holds of each op that touches no memory and of every
$`\mathsf{alloca}`, the one core op that does. So the core dialect meets
an obligation with memory op by op: an op that touches no memory by its
{ref "The-fir-specification--Memory--The-core___s-rules-with-memory"}[tie]
to the set monad, and $`\mathsf{alloca}` by its own rule. A core op with
an outcome in the set monad touches no memory, since $`\mathsf{alloca}`
has none there.
:::

:::readable Fir.Core.allocaResult Fir.Core.allocaAlloc Fir.Core.alloca_denote (pin := Fir.Core.allocaRule) (pin := Fir.Core.memDenoteAt) (fingerprint := "16790093037791789283")
*Definitions and theorem: $`\mathsf{alloca}` with memory.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad, at the layout entries $`\ell` and naming $`\rho`, the
meaning of $`\mathsf{alloca}_N~k~t~c~a` on its empty operand vector is
its
{ref "The-fir-specification--Memory--Stack-allocation-rules"}[rule]: the
allocation of its units in the memory $`\rho(N)`, with its alignment,
whose pointer $`q` it gives as the one result $`[q]`.
:::

:::readable Fir.Core.alloca_neverUB Fir.Core.alloca_makesNoPoison (pin := Fir.NeverUB) (pin := Fir.MakesNoPoison) (fingerprint := "10422466711704620800")
*Theorems: $`\mathsf{alloca}` is never UB, and gives no poison.* For
every kind, type, count, alignment and memory, $`\mathsf{alloca}` meets
two of the
{ref "The-fir-specification--Execution--Effect-obligations"}[effect obligations]
with memory: it never ends in UB, from any memories, since
{ref "The-fir-specification--Memory--Allocation-in-the-state-layer"}[an allocation]
never does, and its result, a pointer, is never poison.
:::

:::readable Fir.Core.alloca_writesNot Fir.Core.alloca_readsNot Fir.Core.alloca_allocatesNot (pin := Fir.OwnRuleHas) (pin := Fir.WritesNot) (pin := Fir.ReadsNot) (pin := Fir.AllocatesNot) (fingerprint := "1999013275673352346")
*Theorems: $`\mathsf{alloca}` touches memory only by allocating where it
declares.* At every layout $`\ell` and naming $`\rho`, and for every memory
$`y` of the run, $`\mathsf{alloca}_N` by its own rule writes no unit of
$`y` and does not read $`y`. It allocates in no memory $`y` that its
{ref "The-fir-specification--Execution--Effect-sets"}[effect set],
$`\mathsf{allocates}(N)`, named through $`\rho`, leaves out: every
$`y \ne \rho(N)`. Each follows from the
{ref "The-fir-specification--Memory--Allocation-in-the-state-layer"}[allocation's]
own obligation, through the law that mapping a computation's results keeps
it.
:::

:::readable Fir.Core.alloca_memTotal Fir.Core.alloca_memMonotone Fir.Core.alloca_finitelyMany (pin := Fir.MemTotal) (pin := Fir.MemMonotone) (pin := Fir.FinitelyMany) (fingerprint := "7091785943372851561")
*Theorems: $`\mathsf{alloca}` is total and monotone with memory, with one
outcome.* $`\mathsf{alloca}` is
{ref "The-fir-specification--Memory--Totality-with-memory"}[total with memory]:
it has an outcome from any memories. It is
{ref "The-fir-specification--Memory--Monotonicity-with-memory"}[monotone with memory]:
from memories that refine others it gives the same pointer, which refines
itself, and memories that refine the others'. And it has
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many outcomes],
one from any memories.
:::

:::readable Fir.Core.alloca_memPropagates Fir.Core.alloca_memReturnsOnDefined (pin := Fir.MemPropagatesPoison) (pin := Fir.MemReturnsOnDefined) (fingerprint := "12654959816609898745")
*Theorems: $`\mathsf{alloca}` meets the poison obligations with memory.*
$`\mathsf{alloca}` has no operands, so no operand is poison, and the
{ref "The-fir-specification--Memory--Poison-obligations-with-memory"}[obligations]
that a poison operand gives poison, or UB by the op's own rules, hold with
nothing to show. And it returns a result on its operand vector with no
poison, the empty one, from memories inside a call: from the empty memories
with one frame entered, it allocates and gives the pointer.
:::
