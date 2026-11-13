import VersoManual
import Fir.Execution.MemoryState
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the state layer, which renders
`Fir.Execution.MemoryState` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The state layer: readable blocks" =>

:::moduleDocs (fingerprint := "4546578974901252582")
:::

:::readable Fir.instMonadChoiceStateT Fir.instMonadUBStateT Fir.instMonadFrameStateT Fir.instMonadMemoryStateT Fir.MonadMorphism.state (fingerprint := "2883893951779013492")
*Definition: the state layer.* Over a monad $`m`, a computation of the
state layer takes the memories $`S` before it, and is a computation of
$`m` whose results are pairs $`(a, S')` of a result and the memories
after it. Its effects are:

* a choice of $`w` bits is $`m`'s, and keeps $`S`;
* UB is $`m`'s: it ends the path, which then shows no memory;
* a frame runs $`x` from $`\mathrm{enter}(S)`, and leaves the call on the
  memories $`x` ends with:
  $$`\mathrm{frame}(x)(S) = \mathrm{map}_{(a, S') \mapsto (a, \mathrm{exit}(S'))}(x(\mathrm{enter}(S)))`
* the memory effect runs the
  {ref "The-fir-specification--Memory--The-memories-of-a-run"}[operations on the memories of a run];
  allocating and freeing never fault, and a load or a store that faults
  is $`m`'s UB with the fault's reason.

*Definition: a translation through the layer.* A monad morphism
$`\varphi` from $`m` to $`n` gives one from the state layer over $`m` to
the state layer over $`n`: it translates each computation at each state,
$`x \mapsto (S \mapsto \varphi(x(S)))`.
:::

:::readable Fir.MonadMorphism.state_mapsFrame Fir.MonadMorphism.state_choose Fir.MonadMorphism.state_ub (fingerprint := "13676839641991408209")
*Theorem: a translation through the layer keeps its effects.* It keeps
frames, since a frame of the layer is built from the monad's own steps.
It keeps a choice of $`w` bits when $`\varphi` keeps it, and UB when
$`\varphi` keeps UB.
:::

:::readable Fir.MonadMorphism.state_keeps (pin := Fir.MonadMorphism.KeepsChoiceUB) (fingerprint := "10206560632729164557")
*Theorem: a translation that keeps choice and UB keeps them through the
layer.* When $`\varphi` keeps choice and UB, so does its translation
through the layer, by the two theorems above.
:::

:::readable Fir.MonadMorphism.state_alloc Fir.MonadMorphism.state_free Fir.MonadMorphism.state_load Fir.MonadMorphism.state_store (fingerprint := "5667444096861358501")
*Theorem: a translation through the layer keeps the memory effect.* It
keeps allocating and freeing, which end at once with a value. It keeps
loads and stores when $`\varphi` keeps UB, since an access either ends at
once with a value or is UB.
:::

:::readable Fir.ChoiceTree.toSetState Fir.ChoiceTree.toSetState_choose Fir.ChoiceTree.toSetState_ub Fir.Func.run_toSetState (fingerprint := "10281720526205955575")
*Definition: the set of a tree, with memory.* The
{ref "The-fir-specification--Execution--Choice-trees"}[set of a tree],
$`\mathrm{set}`, translated through the layer, maps the state layer over
the tree of choices to the state layer over the set monad. It keeps
frames, a choice of bits and UB, since $`\mathrm{set}` keeps the choice
and UB of a tree. So, by the
{ref "The-fir-specification--Execution--Monad-morphisms"}[interpreter's morphism theorem],
the run of a function in the layer over the tree has, at each state, the
run in the layer over the set monad as its set, when each op's semantics
in the one has its semantics in the other as its set.
:::

:::readable Fir.ChoiceTree.toSetState_keeps (fingerprint := "11139396066526368901")
*Theorem: the set of a tree keeps choice and UB through the layer.* The
set of a tree, translated through the layer, keeps choice and UB, since
$`\mathrm{set}` keeps them.
:::
