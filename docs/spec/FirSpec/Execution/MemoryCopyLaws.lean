import VersoManual
import Fir.Execution.MemoryCopyLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on copies of units in the state layer,
which renders `Fir.Execution.MemoryCopyLaws` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "Copies of units in the state layer: readable blocks" =>

:::moduleDocs (fingerprint := "569326385043553866")
:::

:::readable Fir.Memory.Memories.copy Fir.copyUnits (pin := Fir.Memory.Memories.load) (pin := Fir.Memory.Memories.store) (fingerprint := "11199979554107459263")
*Definitions: a copy of units.* A copy of $`n` units of the memory $`x`
from $`q` to $`p` loads $`n` units of $`x` through $`q`, an access aligned
to $`\alpha` units, then stores the units $`\vec{y}` it gave through $`p`,
aligned to $`\alpha'`, in $`x` again. On the memories of a run it gives
the memories that the store gives, or the fault of the load, else of the
store. In a monad with the
{ref "The-fir-specification--Memory--The-memory-effect"}[memory effect]
it is the effect's load, then its store:

$$`\mathrm{copy}_x(p, q, n) = \mathrm{load}_x(q, n, \alpha) \mathbin{>\!\!>\!\!=} \lambda \vec{y}.\ \mathrm{store}_x(p, \vec{y}, \alpha')`

The load leaves the memories as they were, so a copy whose ranges overlap
writes what $`q` pointed to before it began. A copy of units is an
access through both pointers, so a copy of no units still faults through
a pointer with no provenance, or into a freed allocation.
:::

:::readable Fir.copyUnits_load Fir.copyUnits_apply (pin := Fir.instMonadMemoryStateT) (fingerprint := "18419824855619742446")
*Theorems: how a copy of units ends.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad, a copy of units ends from the memories $`S` as the store of
$`\vec{y}` from $`S` ends, when the load of $`S` gives the units
$`\vec{y}`, and in UB, for the reason of the load's fault, when it faults.
So it ends in one of two ways: with the memories that the copy of $`S`
gives, or in UB, for the reason of its fault.
:::

:::readable Fir.copyUnits_hasOutcome Fir.copyUnits_finitelyMany (pin := Fir.HasOutcome) (pin := Fir.FinitelyMany) (fingerprint := "721620124852889285")
*Theorems: a copy of units has one outcome.* From any memories a copy of
units has an outcome, so it
{ref "The-fir-specification--Memory--Totality-with-memory"}[always has an outcome],
and at most one that ends, so it has
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many].
:::

:::readable Fir.copyUnits_writesNot Fir.copyUnits_allocatesNot (pin := Fir.WritesNot) (pin := Fir.AllocatesNot) (fingerprint := "10534258331264215629")
*Theorems: a copy of units writes only its own memory.* For every memory
$`y \ne x`, a copy of units in $`x` meets the
{ref "The-fir-specification--Memory--Memory-obligations"}[obligation]
that it writes no unit of $`y`, as its store does. For every memory $`y`,
$`x` included, it neither allocates nor frees in $`y`. Both follow from
the load's and the store's, by the laws of
{ref "The-fir-specification--Memory--Sequences-in-the-state-layer"}[sequences].
:::

:::readable Fir.copyUnits_readsNot (pin := Fir.ReadsNot) (pin := Fir.ReadsNot.Match) (fingerprint := "11374704810397003222")
*Theorem: a copy of units reads only its own memory.* For every memory
$`y \ne x`, a copy of units in $`x` meets the
{ref "The-fir-specification--Memory--Memory-obligations"}[obligation]
that it does not read $`y`. Run from memories $`S`, and from $`S` with
$`y` replaced by a memory $`m` of the same allocations, its load gives the
same units or the same fault in both, since it reads $`x` alone, and its
store then ends in both as a store does that does not read $`y`. It reads
$`x`, its own memory, so a copy declares a read and a write of $`x`.
:::

:::readable Fir.copyUnits_refines (pin := Fir.StateRefinedBy) (fingerprint := "12525378462702029806")
*Theorem: a copy of units is monotone.* From memories $`S'` that
{ref "The-fir-specification--Memory--Refining-memories"}[refine] $`S`, a
copy of units faults for the same reason as from $`S`, or its load gives
units that refine those it gives from $`S`, so its store gives memories
that refine those it gives from $`S`, or faults as that store does, by
the law of refinement of
{ref "The-fir-specification--Memory--Sequences-in-the-state-layer"}[sequences]. So it
is {ref "The-fir-specification--Memory--Monotonicity-with-memory"}[monotone with memory].
:::
