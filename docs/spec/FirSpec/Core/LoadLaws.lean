import VersoManual
import Fir.Core.LoadLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the load obligations, which renders
`Fir.Core.LoadLaws` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Load obligations: readable blocks" =>

:::moduleDocs (fingerprint := "17935804110535287159")
:::

:::readable Fir.Core.loadAccess Fir.Core.load_denote Fir.Core.loadRule_poison Fir.Core.loadRule_value Fir.Core.load_ownRuleHas (pin := Fir.Core.loadRule) (pin := Fir.Core.memDenoteAt) (pin := Fir.OwnRuleHas) (fingerprint := "16366753097556754820")
*Definitions and theorems: $`\mathsf{load}` with memory.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad, at the layout entries $`\ell` and naming $`\rho`, the
meaning of $`\mathsf{load}_N~o~W~a` on the operand $`p` is its
{ref "The-fir-specification--Memory--Load-rules"}[rule]: on poison, UB
from any memories and nothing else; on a pointer $`q`, the
{ref "The-fir-specification--Memory--Loads-in-the-state-layer"}[load]
through $`q` of its units from $`\rho(N)`, with its result decoded. So
what $`\mathsf{load}` runs by its own rule has a property when its rule
has it on every pointer operand.
:::

:::readable Fir.Core.load_writesNot Fir.Core.load_allocatesNot Fir.Core.load_readsNot (pin := Fir.WritesNot) (pin := Fir.ReadsNot) (pin := Fir.AllocatesNot) (fingerprint := "2290644961823691538")
*Theorems: $`\mathsf{load}` touches memory only by reading where it
declares.* At every layout $`\ell` and naming $`\rho`, and for every
memory $`y` of the run, $`\mathsf{load}_N` by its own rule writes no unit
of $`y`, and neither allocates nor frees in $`y`. It does not read any
memory $`y` that its
{ref "The-fir-specification--Execution--Effect-sets"}[effect set],
$`\mathsf{reads}(N)`, named through $`\rho`, leaves out: every
$`y \ne \rho(N)`. On a poison pointer it ends only in UB, for the same
reason from every memories; on a pointer each follows from the
{ref "The-fir-specification--Memory--Loads-in-the-state-layer"}[load's]
own laws, since decoding its units is a function of them alone.
:::

:::readable Fir.Core.load_memTotal Fir.Core.load_finitelyMany (pin := Fir.MemTotal) (pin := Fir.FinitelyMany) (fingerprint := "16711367289581487520")
*Theorems: $`\mathsf{load}` has an outcome, and at most one that ends.*
From any memories, $`\mathsf{load}` ends in UB or gives a value: it is
{ref "The-fir-specification--Memory--Totality-with-memory"}[total with memory].
It has at most one outcome that ends, a value with the memories it
started from, so it has
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many outcomes].
:::

:::readable Fir.Core.load_memMonotone (pin := Fir.MemMonotone) (fingerprint := "14469370388878494581")
*Theorem: $`\mathsf{load}` is monotone with memory.* On a pointer operand
that refines another, from memories that refine others, $`\mathsf{load}`'s
outcomes refine the other's. A poison pointer is UB, which every outcome
refines. A defined pointer is refined only by itself, and from memories
that refine others the load faults for the same reason or loads units that
refine the others', whose decoding
{ref "The-fir-specification--Memory--Laws-of-values-in-units"}[refines]
the others' value.
:::

:::readable Fir.Core.load_memPropagates Fir.Core.load_memReturnsOnDefined (pin := Fir.MemPropagatesPoison) (pin := Fir.MemReturnsOnDefined) (fingerprint := "10694971604290178069")
*Theorems: $`\mathsf{load}` propagates poison with memory, and returns on a
defined pointer.* Its one operand is the pointer, so a poison operand gives
no result, and the UB it gives from memories $`S` is the UB that a pointer
with no provenance in its place gives from $`S`: a load through it faults.
It returns a result on a defined pointer from memories inside a call: a
fresh allocation of the units of $`\mathsf{i}W` at the load's alignment,
in memory $`\rho(N)` of $`\mathsf{Memories.empty}` entered, through the
pointer to it, gives the value its poison units decode to. So
$`\mathsf{load}` meets the
{ref "The-fir-specification--Memory--Poison-obligations-with-memory"}[poison obligations with memory].
:::
