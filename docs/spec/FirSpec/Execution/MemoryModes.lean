import VersoManual
import Fir.Execution.MemoryModes
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on modes with memory, which renders
`Fir.Execution.MemoryModes` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Modes with memory: readable blocks" =>

:::moduleDocs (fingerprint := "5839031385033120517")
:::

:::readable Fir.MonadMorphism.state_lift Fir.MonadMorphism.state_mapsDenote_liftState (fingerprint := "11229248626212830646")
*Theorem: a morphism through the layer keeps lifted computations.* For a
{ref "The-fir-specification--Execution--Monad-morphisms"}[monad morphism]
$`\varphi` from $`m` to $`n` and a computation $`x` of $`m` with no
memory, the morphism through the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] maps
$`x` lifted into the layer to its image lifted:
$`\varphi^{\mathrm{state}}(\mathrm{lift}(x)) = \mathrm{lift}(\varphi(x))`.

*Theorem: it keeps lifted semantics.* So when $`\varphi` maps a dialect's
semantics in $`m` to its semantics in $`n`, it maps its
{ref "The-fir-specification--Memory--Runs-with-memory"}[lifted semantics]
in the layer over $`m` to its lifted semantics in the layer over $`n`, op
by op and terminator by terminator.
:::

:::readable Fir.Func.memTree (pin := Fir.Memory.Memories.empty) (fingerprint := "2604371483722788827")
*Definition: the tree of a run with memory.* Where the units of the memory
$`x` are $`u(x)` bits wide, the tree of a run with memory of the function
$`f` of the module $`M` on $`\vec{v}` with $`k` steps is its run in the
state layer over the
{ref "The-fir-specification--Execution--Choice-trees"}[tree of choices],
by the dialect's semantics there, from the empty memories, with the
memories dropped at the end of each path:

$$`\mathrm{tree}^{\mathrm{mem}}_{M,f}(\vec{v}, k) = \mathrm{map}_{(r, S) \mapsto r}(\mathrm{run}_{M,f}(\vec{v}, k)(\emptyset))`

An observer sees what a run returns and not its memories, until
observations at the end of a run are designed (#233). This is the tree
that the {ref "The-fir-specification--Execution--Exhaustive___-scripted-and-sampled-modes"}[modes]
walk.
:::

:::readable Fir.MemMapsDenote Fir.Func.memTree_toSet (pin := Fir.Func.memRuns) (fingerprint := "1030219016229167072")
*Definition: the semantics in the tree denotes the semantics with memory.*
At a naming $`\rho` of the dialect's memories, its semantics in the layer
over the tree of choices _denotes_ its
{ref "The-fir-specification--Memory--Memory-obligations"}[semantics with memory]
when the set of a tree, translated through the layer, maps each op's
computation in the one to its computation in the other.

*Theorem: the tree of a run with memory has the run with memory as its
set.* When it does, for every module $`M`, function $`f`, arguments
$`\vec{v}` and fuel $`k`, the set of
$`\mathrm{tree}^{\mathrm{mem}}_{M,f}(\vec{v}, k)` is the
{ref "The-fir-specification--Memory--Runs-with-memory"}[run with memory]
of $`f` at $`\rho`, on $`\vec{v}` at fuel $`k`. The proof is the
{ref "The-fir-specification--Execution--Monad-morphisms"}[interpreter's morphism theorem]
through the layer, at the empty memories, and the set of a tree keeps
mapping a function over its results.
:::

:::readable Fir.Func.memExplore_outcomes Fir.Func.memExplore_stuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "15645183375014906706")
*Theorem: exhaustive mode gives exactly the outcomes of a run with
memory.* When the semantics in the tree denotes the semantics with memory
at $`\rho`, for every module $`M`, function $`f`, arguments $`\vec{v}`,
fuel $`k` and choice budget $`B`, let $`R_k` be the run with memory of
$`f` at $`\rho` on $`\vec{v}` at fuel $`k`. If exhaustive mode on
$`\mathrm{tree}^{\mathrm{mem}}_{M,f}(\vec{v}, k)` with budget $`B` gives
the list $`L`, then for every outcome $`o`,

$$`o \in \mathrm{out}(R_k) \iff \exists (\ell, c) \in L.\ \mathrm{path\_end}(\ell) = \mathsf{outcome}~o`

*Theorem: it lists a stuck path exactly when the run has one.* With the
same hypotheses, $`R_k` is stuck exactly when some leaf of $`L` has the
path end $`\mathsf{stuck}~s`, for some $`s`. Both follow from the theorem
above and exhaustive mode's theorem on any tree.
:::

:::readable Fir.Func.memScript_outcomes Fir.Func.memScript_stuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "12084616605611518175")
*Theorem: on a sequence that fits, scripted mode gives an outcome of a run
with memory.* With the same hypotheses, for every $`\mathrm{read}` and
choice sequence $`\mathit{cs}`, if scripted mode on
$`\mathrm{tree}^{\mathrm{mem}}_{M,f}(\vec{v}, k)` following
$`\mathit{cs}`, from no choices made, reaches the leaf $`\ell` with no
misfit, and $`\mathrm{path\_end}(\ell) = \mathsf{outcome}~o`, then
$`o \in \mathrm{out}(R_k)`.

*Theorem: it reports a stuck path only when the run has one.* If
$`\mathrm{path\_end}(\ell) = \mathsf{stuck}~s`, then $`R_k` is stuck.
:::
