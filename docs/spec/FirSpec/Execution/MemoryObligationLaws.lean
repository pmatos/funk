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

:::moduleDocs (fingerprint := "923162801911803003")
:::

:::readable Fir.MemSet.map_map Fir.append_nil (fingerprint := "5109573099865184236")
*Theorem: renaming twice.* Renaming the memories of a set by $`f` and then
by $`g` renames them by $`g \circ f`. A list followed by nothing is the
list: $`l \mathbin{+\!\!+} [] = l`.
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

:::readable Fir.writesNot_lift Fir.allocatesNot_lift Fir.readsNot_lift (fingerprint := "16615654636980269060")
*Theorem: a computation with no memory meets every memory obligation.* A
computation of the set monad, run in the state layer, ends with the
memories it started with. So it writes no unit of any memory, neither
allocates nor frees in any memory, and reads no memory: from
$`S[x := m]` it ends as it ends from $`S`, with $`S[x := m]`, which agrees
with $`S` off $`x` and whose units of $`x` are those of $`m`.
:::

:::readable Fir.WritesNot.map Fir.AllocatesNot.map Fir.ReadsNot.map (fingerprint := "11300524075204757905")
*Theorem: mapping the results keeps the obligations.* If $`c` writes no
unit of $`x`, neither allocates nor frees in $`x`, or does not read $`x`,
then so does $`f \mathbin{<\$>} c`, for every $`f`: mapping changes the
results and not the memories.
:::

:::readable Fir.DialectMemDenote.ofSetM Fir.DialectMemDenote.ofSetM_writesNot Fir.DialectMemDenote.ofSetM_readsNot Fir.DialectMemDenote.ofSetM_allocatesNot (fingerprint := "16265963236920106000")
*Definition: the semantics with memory of a dialect whose ops touch no
memory.* At every naming $`\rho`, each op runs by its rule in the set
monad, lifted into the state layer, and keeps the memories.

*Theorem: such a dialect meets the memory obligations.* At every naming
$`\rho` and for every memory $`x` of the run, what each of its ops runs by
its own rule writes no unit of $`x`, does not read $`x`, and neither
allocates nor frees in $`x`, whatever the op declares.
:::
