import VersoManual
import Fir.Execution.MemoryObligationLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on meeting the memory obligations, which
renders `Fir.Execution.MemoryObligationLaws` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "Meeting the memory obligations: readable blocks" =>

:::moduleDocs (fingerprint := "17715756551949538059")
:::

:::readable Fir.MemSet.map_map Fir.prefix_refl (fingerprint := "1913305905240732111")
*Theorem: renaming twice.* Renaming the memories of a set by $`f` and then
by $`g` renames them by $`g \circ f`. A list is a prefix of itself.
:::

:::readable Fir.SetM.lift_apply Fir.SetM.stateMap_apply (fingerprint := "1188090380208771038")
*Theorem: how a lifted or mapped computation ends.* A computation $`x` of
the set monad, run in the state layer from $`S`, ends in
$`\mathsf{ok}~(a, S)` for each $`\mathsf{ok}~a \in x`, and in
$`\mathsf{ub}~r` for each $`\mathsf{ub}~r \in x`. A computation $`c` of the
state layer with its results mapped by $`f` ends in
$`\mathsf{ok}~(f(a), S')` for each $`\mathsf{ok}~(a, S') \in c(S)`, and in
UB as $`c` does.
:::

:::readable Fir.writesNot_lift Fir.allocatesNot_lift Fir.readsNot_lift (fingerprint := "13836026313982123487")
*Theorem: a computation with no memory meets every memory obligation.* A
computation of the set monad, run in the state layer, ends with the
memories it started with. So it writes no unit of any memory, neither
allocates nor frees in any memory, and reads no memory: from
$`S[x := m]` it ends as it ends from $`S`, with $`S[x := m]`, which agrees
with $`S` off $`x` and whose units of $`x` are those of $`m`.
:::

:::readable Fir.WritesNot.map Fir.AllocatesNot.map Fir.ReadsNot.map (fingerprint := "16699392017965335039")
*Theorem: mapping the results keeps the obligations.* If $`c` writes no
unit of $`x`, neither allocates nor frees in $`x`, or does not read $`x`,
then so does $`f \mathbin{<\$>} c`, for every $`f`: mapping changes the
results and not the memories.
:::

:::readable Fir.DialectMemDenote.ofSetM Fir.DialectMemDenote.ofSetM_writesNot Fir.DialectMemDenote.ofSetM_readsNot Fir.DialectMemDenote.ofSetM_allocatesNot (fingerprint := "7522058415703922555")
*Definition: the semantics with memory of a dialect whose ops touch no
memory.* At every naming $`\rho`, each op runs by its rule in the set
monad, lifted into the state layer, and keeps the memories.

*Theorem: such a dialect meets the memory obligations.* At every naming
$`\rho` and for every memory $`x` of the run, what each of its ops runs by
its own rule writes no unit of $`x`, does not read $`x`, and neither
allocates nor frees in $`x`, whatever the op declares.
:::

:::readable Fir.NoUB.map Fir.noUB_lift Fir.NoUB.of_lift (fingerprint := "15877855276453459811")
*Theorems: no UB through mapping and lifting.* Mapping the results of a
computation that never ends in UB gives one that never does. A computation
$`x` of the set monad with $`\mathsf{ub}~r \notin x` for every $`r` never
ends in UB in the state layer; and if, lifted into the layer, it never ends
in UB from some memories, then $`\mathsf{ub}~r \notin x` for every $`r`.
:::

:::readable Fir.DialectMemDenote.ofSetM_liftsSetM Fir.NeverUB.ofSetM Fir.MakesNoPoison.ofSetM (pin := Fir.LiftsSetM) (fingerprint := "14711993354742054684")
*Theorem: a dialect whose ops touch no memory lifts the set monad.* Its
semantics with memory is its semantics in the set monad, lifted, at every
naming: the two are
{ref "The-fir-specification--Memory--Runs-with-memory"}[tied].

*Theorem: its effects with memory are its effects in the set monad.* An
op of such a dialect that never ends in UB in the set monad never ends in
UB with memory, at every naming and from every memories, and one that
makes no poison in the set monad makes none with memory.
:::

:::readable Fir.OwnRuleHas.ofLifts Fir.NeverUB.ofLifts Fir.MakesNoPoison.ofLifts (pin := Fir.OpLiftsSetM) (fingerprint := "8931742395573466083")
*Theorems: the obligations of an op that touches no memory.* What an op
that is
{ref "The-fir-specification--Memory--Runs-with-memory"}[tied] runs by its
own rule has every property that each computation of the set monad, lifted
into the layer, has: so it writes, reads and allocates in no memory, at
every layout and naming. If it never ends in UB in the set monad, it never
does with memory, and if it makes no poison in the set monad, it makes none
with memory. The core dialect meets its effect obligations so, op by op.
:::

:::readable Fir.NeverUB.setM Fir.MakesNoPoison.setM (pin := Fir.LiftsSetM) (fingerprint := "11426148675706650251")
*Theorem: back to the set monad.* In a dialect whose semantics with memory
lifts its semantics in the set monad, an op that never ends in UB with
memory never ends in UB in the set monad, and one that makes no poison
with memory makes none in the set monad. The proof runs the op from the
empty memories of a run whose one memory name is $`()`. So the theorems
over runs in the set monad, such as the soundness of function summaries,
use the obligations through this tie.
:::
