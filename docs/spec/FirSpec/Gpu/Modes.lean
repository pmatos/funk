import VersoManual
import Fir.Gpu.Modes
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the modes of the core and `gpu`,
which renders `Fir.Gpu.Modes` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Modes of the core and gpu: readable blocks" =>

:::moduleDocs (fingerprint := "8818943503202945511")
:::

:::readable Fir.Gpu.memName (fingerprint := "15817030782446627946")
*Definition: the run's names for the sum's memories.* `gpu` has no memory
of its own, so each memory of the sum is a core memory, and the run names
it by its number, as the core's modes do. Work-group memory is the memory
of the host's layout that an allocation's result names.
:::

:::readable Fir.Gpu.treeDenote Fir.Gpu.memTreeDenote (fingerprint := "13793003816320139418")
*Definition: the sum's rules in the tree of choices.* In the state layer
over the tree of choices, a question of `gpu` gives its results and keeps
the memories, and an allocation allocates for the whole run by its rule
with memory. A core op runs by the core's rules with memory in the tree, where
the run names each core memory as the sum does and gives each op the items
it gives the sum's ops; an op with no rule ends its path with no outcome,
naming that op.
:::

:::readable Fir.Gpu.treeMapsDenote Fir.Gpu.memMapsDenote (fingerprint := "3656392835769362579")
*Theorems: the tree denotes the runs with memory.* Taking the set of each
path through the state layer keeps a result, the memories and an
allocation, so it maps the rules of `gpu` in the tree to its rules with
memory, and so, with the core's, the sum's rules in the tree to
its rules with memory, at every layout and naming of the sum's memories
and every record of items.
:::

:::readable Fir.Gpu.modeTree Fir.Gpu.Leaf Fir.Gpu.exhaustive Fir.Gpu.scripted Fir.Gpu.sampled (pin := Fir.ChoiceTree.explore) (pin := Fir.ChoiceTree.script) (pin := Fir.ChoiceTree.sample) (pin := Fir.Func.memTree) (fingerprint := "15012274531061140136")
*Definition: the modes on a function of the sum.* At a work-item, for a
function $`f` of a module $`M` of the sum, arguments $`\vec{v}` and fuel
$`k`, the tree of $`f`'s run is its run with memory in the tree of choices,
from the memories that hold the globals of $`M`'s own table, where each
memory has its entry in $`M`'s data layout, the run names the sum's
memories by their numbers, and it gives each op the items of $`M`'s own
table. A leaf of the
tree is how a path ends. Exhaustive, scripted and sampled mode walk the
tree as they walk the core's. `fir-ref run` computes these three, and the
walk that tries a few NaNs below, on a function of the module or a kernel
of a nested module run in the module of its table, and nothing else.
:::

:::readable Fir.Gpu.exhaustive_memOutcomes Fir.Gpu.exhaustive_memStuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "8181067986880042047")
*Theorems: exhaustive mode gives exactly the outcomes.* At every
work-item, within its choice budget, exhaustive mode on a function of the
sum lists exactly the outcomes of its run with memory at the fuel it runs
with, where the run gives each op the items of the module's own table, and
lists a stuck path exactly when the run has one.
:::

:::readable Fir.Gpu.exhaustiveNaN (pin := Fir.ChoiceTree.exploreNaN) (fingerprint := "16034180316266426603")
*Definition: the walk that tries a few NaNs on a function of the sum.* At a
work-item, with the numbers $`\vec{n}`, it walks the tree of the run as
the {ref "The-fir-specification--Memory--Exhaustive-runs-that-try-a-few-NaNs"}[walk that tries a few NaNs]
does. `fir-ref run --exhaustive --nans` computes it (ADR-2026-11-16-0855).
:::

:::readable Fir.Gpu.exhaustiveNaN_memOutcomes Fir.Gpu.exhaustiveNaN_memStuck Fir.Gpu.exhaustiveNaN_exact (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "9093896156544042412")
*Theorems: the walk that tries a few NaNs gives outcomes, and all of them
without a NaN choice.* At every work-item, each outcome that it lists on a
function of the sum, and each stuck path, is one of its run with memory at
the fuel it runs with. When no path that it lists made a NaN choice, it
lists exactly the outcomes of the run.
:::

:::readable Fir.Gpu.scripted_memOutcomes Fir.Gpu.scripted_memStuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "9716923664382066425")
*Theorems: scripted mode gives an outcome.* At every work-item, on a choice
sequence that fits, scripted mode on a function of the sum gives an outcome
of its run with memory, and reports a stuck path only when the run has one.
:::

:::readable Fir.Gpu.sampled_fits Fir.Gpu.sampled_memOutcomes Fir.Gpu.sampled_memStuck (pin := Fir.ChoiceTree.readChosen) (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "13396497027260275280")
*Theorems: sampled mode gives an outcome.* The values that sampled mode
chose are a choice sequence that fits the run: scripted mode on them reports
the same path, with as many choices. So, whatever the generator, sampled
mode gives an outcome of the run with memory, and reports a stuck path only
when the run has one.
:::
