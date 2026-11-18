import VersoManual
import Fir.Execution.MemoryLoadLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on loads in the state layer, which
renders `Fir.Execution.MemoryLoadLaws` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Loads in the state layer: readable blocks" =>

:::moduleDocs (fingerprint := "4607958562880319941")
:::

:::readable Fir.load_apply Fir.load_keeps (pin := Fir.instMonadMemoryStateT) (pin := Fir.Memory.Memories.load) (fingerprint := "453037277487555865")
*Theorems: how a load ends.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad, the
{ref "The-fir-specification--Memory--The-memory-effect"}[memory effect]'s
load of $`n` units of the memory $`x` through $`p`, aligned to $`\alpha`
units, ends from the memories $`S` in one of two ways: with the units
$`\vec{x}` that the aligned load of $`S`'s memory $`x` gives, and the
memories $`S` unchanged; or in UB, for the reason of the fault that the
aligned load gives. A load that ends keeps the memories.
:::

:::readable Fir.load_hasOutcome Fir.load_finitelyMany (pin := Fir.HasOutcome) (pin := Fir.FinitelyMany) (fingerprint := "362270803784232374")
*Theorems: a load has one outcome.* From any memories a load has an
outcome, so it
{ref "The-fir-specification--Memory--Totality-with-memory"}[always has an outcome],
and at most one that ends, so it has
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many].
:::

:::readable Fir.load_writesNot Fir.load_allocatesNot (pin := Fir.WritesNot) (pin := Fir.AllocatesNot) (fingerprint := "2640054746864991937")
*Theorems: a load changes no memory.* For every memory $`y`, a load meets
the {ref "The-fir-specification--Memory--Memory-obligations"}[obligations]
that it writes no unit of $`y`, and neither allocates nor frees in $`y`:
a path that ends keeps the memories.
:::

:::readable Fir.load_readsNot (pin := Fir.ReadsNot) (pin := Fir.ReadsNot.Match) (fingerprint := "15605190028077751865")
*Theorem: a load reads only its own memory.* For every memory $`y \ne x`,
a load of $`x` meets the
{ref "The-fir-specification--Memory--Memory-obligations"}[obligation]
that it does not read $`y`. Run from memories $`S`, and from $`S` with
$`y` replaced by a memory $`m` of the same allocations, it faults for the
same reason in both, or loads the same units in both, since the memory
$`x` is the same; each run ends with the memories it started from, which
agree off $`y`, and whose units of $`y` are those each run had.
:::

:::readable Fir.load_refines (pin := Fir.StateRefinedBy) (pin := Fir.Memory.Memories.IsRefinedBy) (fingerprint := "16922641767448538274")
*Theorem: a load is monotone.* From memories $`S'` that
{ref "The-fir-specification--Memory--Refining-memories"}[refine] $`S`, a
load faults for the same reason as from $`S`, or loads units that refine
those it loads from $`S`, with $`S'` and $`S` unchanged. So it is
{ref "The-fir-specification--Memory--Monotonicity-with-memory"}[monotone with memory],
its units refined unit by unit.
:::
