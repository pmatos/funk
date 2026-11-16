import VersoManual
import Fir.Sum.RunLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the runs of a sum, op by op, which
renders `Fir.Sum.RunLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Runs of a sum, op by op: readable blocks" =>

:::moduleDocs (fingerprint := "7172749819183214281")
:::

:::readable Fir.Dialect.sum.mapsDenote (fingerprint := "2955957549720364140")
*Theorem: a morphism maps a sum's semantics.* Let $`\varphi` be a monad
morphism from $`m` to $`n`. If $`\varphi` maps the base's semantics in
$`m` to its semantics in $`n`, op by op, and maps the extension's so too,
then it maps the sum's: a base op's results are mapped to the sum's types,
and a morphism keeps mapping. So the tree of a run of the sum, which the
modes walk, has the sum's run with memory as its set when each side's tree
has its side's.
:::

:::readable Fir.Dialect.sum.opLiftsSetM_inl (fingerprint := "13497951755608605084")
*Theorem: a tied base op is tied in the sum.* An op of the base that runs
with memory by its rule in the set monad and keeps the memories does so in
the sum, wherever a run names the sum's memories: mapping its results to the
sum's types commutes with lifting it into the state layer.
:::

:::readable Fir.FinitelyMany.map Fir.Dialect.sum.opsFinite (fingerprint := "659648607149736864")
*Theorems: a sum's ops have finitely many outcomes.* Mapping the results of
a computation with memory keeps finitely many outcomes. So when each op of
the base has finitely many outcomes with memory, where the run names the
base's memories as the sum does, and each op of the extension does, each op
of the sum that runs by its own rule does.
:::

:::readable Fir.MemSet.has_map Fir.Effects.TouchesNoMemory.of_map Fir.Dialect.sum.opsIgnoreMemory (fingerprint := "3896705368860678614")
*Theorems: a sum's ops ignore the memories where they touch none.* A set of
memories holds the new name of each memory it holds once its memories are
renamed, so a set of effects that touches no memory once renamed touches
none before. A base op's effects in the sum are its own, with each memory
renamed to the sum's name for it, and mapping the results keeps a
computation that ignores the memories. So when each op of the base ignores
the memories where it declares no memory effect, where the run names the
base's memories as the sum does, and each op of the extension does, each
op of the sum that runs by its own rule does.
:::
