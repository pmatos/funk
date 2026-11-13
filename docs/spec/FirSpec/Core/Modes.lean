import VersoManual
import Fir.Core.Modes
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core dialect's modes, which
renders `Fir.Core.Modes` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The core dialect's modes: readable blocks" =>

:::moduleDocs (fingerprint := "6302047697601312163")
:::

:::readable Fir.Core.modeTree Fir.Core.exhaustive Fir.Core.scripted (pin := Fir.ChoiceTree.explore) (pin := Fir.ChoiceTree.script) (pin := Fir.Func.memTree) (fingerprint := "10641358420631129298")
*Definition: exhaustive and scripted mode on a core function.* For a core
function $`f` of a module $`M`, arguments $`\vec{v}` of its parameter
types and fuel $`k`, let
$`T = \mathrm{tree}^{\mathrm{mem}}_{M,f}(\vec{v}, k)` be the
{ref "The-fir-specification--Memory--Modes-with-memory"}[tree of its run with memory],
from the empty memories, where each memory $`n` of the run has
$`\ell_M(n)`, its entry in $`M`'s
{ref "The-fir-specification--Abstract-syntax--Data-layouts"}[data layout], and
the run names the core's memories by themselves:

* $`\mathrm{exhaustive}(M, f, \vec{v}, k, B)` is exhaustive mode, with
  the choice budget $`B`, on $`T`: every path's leaf and number of
  choices, or a failure when some path chooses more than $`B` bits in all.
* $`\mathrm{scripted}(M, f, \vec{v}, k, \mathit{cs})` is scripted mode
  on $`T`, following the choice sequence $`\mathit{cs}`, each value read
  by a given $`\mathrm{read}`, from no choices made: the leaf it reaches
  and its number of choices, or why $`\mathit{cs}` does not fit.

`fir-ref` computes these, and sampled mode below, and nothing else, to
report a run. So it runs a module with the units, byte orders and pointer
widths that its own layout declares
(`docs/decisions/fir-ref-memory.md#the-modes-run-with-memory`).
:::

:::readable Fir.Core.sampled (pin := Fir.ChoiceTree.sample) (fingerprint := "9196970832482429634")
*Definition: sampled mode on a core function.* For a function
$`\mathrm{draw}` and a generator $`g`,
$`\mathrm{sampled}(M, f, \vec{v}, k, g)` is sampled mode on the tree of
the run with memory of $`f` on $`\vec{v}` with $`k` steps of fuel: the
leaf of the path on which $`\mathrm{draw}` gives each choice, from
$`g`, and the values chosen on it, in order.
:::

:::readable Fir.Core.exhaustive_memOutcomes Fir.Core.exhaustive_memStuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "16935694772507166305")
*Theorem: exhaustive mode gives exactly the outcomes of a core run with
memory.* For every module $`M`, function $`f`, arguments $`\vec{v}`,
fuel $`k` and choice budget $`B`, let $`R^M_k` be the
{ref "The-fir-specification--Memory--Runs-with-memory"}[run with memory]
of $`f` on $`\vec{v}`, at fuel $`k`, where each memory has its entry in
$`M`'s data layout and the run names the core's memories by themselves. If
$`\mathrm{exhaustive}(M, f, \vec{v}, k, B)` gives the list $`L`, then
for every {ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[outcome] $`o`,
with $`\mathrm{path\_end}` the
{ref "The-fir-specification--Execution--Exhaustive___-scripted-and-sampled-modes"}[path end]
of a leaf,

$$`\begin{aligned} & o \in \mathrm{out}(R^M_k) \iff \\ & \quad \exists (\ell, c) \in L.\ \mathrm{path\_end}(\ell) = \mathsf{outcome}~o \end{aligned}`

*Theorem: it lists a stuck path exactly when the run has one.* With the
same hypotheses, $`R^M_k` is stuck exactly when some leaf of $`L` has
the path end $`\mathsf{stuck}~s`, for some $`s`. Both are the
{ref "The-fir-specification--Memory--Modes-with-memory"}[theorems of modes with memory],
since the core's semantics in the tree denotes its semantics with memory.
:::

:::readable Fir.Core.scripted_memOutcomes Fir.Core.scripted_memStuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "12524770038561540077")
*Theorem: on a sequence that fits, scripted mode gives an outcome of a
core run with memory.* For every $`\mathrm{read}`, module $`M`, function
$`f`, arguments $`\vec{v}`, fuel $`k` and choice
sequence $`\mathit{cs}`, if
$`\mathrm{scripted}(M, f, \vec{v}, k, \mathit{cs})` reaches the leaf
$`\ell`, with no misfit, and
$`\mathrm{path\_end}(\ell) = \mathsf{outcome}~o`, then
$`o \in \mathrm{out}(R^M_k)`.

*Theorem: it reports a stuck path only when the run has one.* With the
same hypotheses, if $`\mathrm{path\_end}(\ell) = \mathsf{stuck}~s`,
then $`R^M_k` is stuck.
:::

:::readable Fir.Core.sampled_fits (pin := Fir.ChoiceTree.readChosen) (fingerprint := "6811916062769141243")
*Theorem: the values that sampled mode chose fit the run.* For every
$`\mathrm{draw}`, module $`M`, function $`f`, arguments
$`\vec{v}`, fuel $`k` and generator $`g`, let
$`\mathrm{sampled}(M, f, \vec{v}, k, g)` give the leaf $`\ell` and the
values $`\mathit{cs}`. Then scripted mode on $`\mathit{cs}`, reading
chosen values back, reaches $`\ell` after $`|\mathit{cs}|` choices, the
length of $`\mathit{cs}`:

$$`\mathrm{scripted}(M, f, \vec{v}, k, \mathit{cs}) = (\ell,\ |\mathit{cs}|)`

So a sampled run can be replayed exactly, from the values `fir-ref`
reports.
:::

:::readable Fir.Core.sampled_memOutcomes Fir.Core.sampled_memStuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "12480977525883664790")
*Theorem: sampled mode gives an outcome of a core run with memory,
whatever the generator.* For every $`\mathrm{draw}`, module $`M`, function
$`f`, arguments $`\vec{v}`, fuel $`k` and generator
$`g`, if the leaf $`\ell` that $`\mathrm{sampled}(M, f, \vec{v}, k, g)`
gives has $`\mathrm{path\_end}(\ell) = \mathsf{outcome}~o`, then
$`o \in \mathrm{out}(R^M_k)`.

*Theorem: it reports a stuck path only when the run has one.* With the
same hypotheses, if $`\mathrm{path\_end}(\ell) = \mathsf{stuck}~s`,
then $`R^M_k` is stuck. Both follow from scripted mode's theorems,
since the values sampled mode chose fit the run.
:::
