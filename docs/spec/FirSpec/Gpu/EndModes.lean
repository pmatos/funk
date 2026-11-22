import VersoManual
import Fir.Gpu.EndModes
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the modes of the core and `gpu` that
see the end of a return, which renders `Fir.Gpu.EndModes`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Modes of the core and gpu that see the end of a return: readable blocks" =>

:::moduleDocs (fingerprint := "9725111358824139138")
:::

:::readable Fir.Gpu.RunEnd Fir.Gpu.EndLeaf Fir.Gpu.endTree Fir.Gpu.exhaustiveEnd Fir.Gpu.exhaustiveNaNEnd Fir.Gpu.scriptedEnd Fir.Gpu.sampledEnd (pin := Fir.ObservedEnd) (pin := Fir.Func.memEndTree) (pin := Fir.ChoiceTree.explore) (pin := Fir.ChoiceTree.exploreNaN) (pin := Fir.ChoiceTree.script) (pin := Fir.ChoiceTree.sample) (fingerprint := "11307820692733739624")
*Definition: the modes on a function of the sum that see the end of each
return.* At a work-item, for a function $`f` of a module $`M` of the sum,
arguments $`\vec{v}` and fuel $`k`, the tree is the tree of $`f`'s run with
memory that sees each return at its end, from the memories that hold the
globals of $`M`'s own table, where each memory has its entry in $`M`'s
data layout and the run names the sum's
memories by their numbers. The end of a return compares no addresses, and
the memory numbered $`n` is the memory $`n` of the run. Exhaustive mode,
the walk that tries a few NaNs, scripted mode and sampled mode walk this
tree as they walk the tree that sees a return as its values.
`fir-ref run --world` computes these four.
:::

:::readable Fir.Gpu.exhaustiveEnd_memOutcomes Fir.Gpu.exhaustiveNaNEnd_memOutcomes Fir.Gpu.scriptedEnd_memOutcomes Fir.Gpu.sampledEnd_memOutcomes (pin := Fir.Run.outcomes) (pin := Fir.ChoiceTree.Leaf.pathEnd) (pin := Fir.Func.memEndRuns) (fingerprint := "8471554738724013232")
*Theorems: the modes give the outcomes of the run with memory, seen at
their ends.* At every work-item, within its choice budget, exhaustive mode
on a function of the sum lists exactly the outcomes of its run with memory
at the fuel it runs with, each return seen at its end. Each outcome that
the walk that tries a few NaNs lists is one of them, and all of them when
no path it lists made a NaN choice. Scripted mode on a sequence that fits
gives one of them, and so does sampled mode, whatever the generator: the
values it draws are a sequence that fits the run.
:::

:::readable Fir.Gpu.observedRuns_of_memEnd (pin := Fir.Func.observedRuns) (fingerprint := "13169224003855173792")
*Theorem: a return or UB that a mode reports is an outcome of the spec's
traced runs.* Neither the core nor `gpu` shows an event, so a return or UB
of a function's run with memory at some fuel, each return seen at its end,
is an outcome of its traced runs at the module's layout, with an empty
trace, where the end of a return compares no addresses.
:::
