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

:::moduleDocs (fingerprint := "14893464455767568293")
:::

:::readable Fir.instMonadChoiceStateT Fir.instMonadUBStateT Fir.instMonadFrameStateT Fir.instMonadMemoryStateT Fir.MonadMorphism.state (fingerprint := "8937651886765150919")
*Definition: the state layer.* Over a monad $`m`, a computation of the
state layer takes the memories $`S` before it, and is a computation of
$`m` whose results are pairs $`(a, S')` of a result and the memories
after it. Its effects are:

* a choice of $`w` bits is $`m`'s, and keeps $`S`, and so is a NaN choice;
* UB is $`m`'s: it ends the path, which then shows no memory;
* a frame runs $`x` from $`\mathrm{enter}(S)`, and leaves the call on the
  memories $`x` ends with:
  $$`\mathrm{frame}(x)(S) = \mathrm{map}_{(a, S') \mapsto (a, \mathrm{exit}(S'))}(x(\mathrm{enter}(S)))`
* the memory effect runs the
  {ref "The-fir-specification--Memory--The-memories-of-a-run"}[operations on the memories of a run];
  allocating and freeing never fault, a load or a store is the aligned
  access of the alignment it is given, and one that faults, misaligned
  included, is $`m`'s UB with the fault's reason. Exposing gives what
  {ref "The-fir-specification--Memory--Address-policies"}[exposing a pointer]
  gives, and is $`m`'s UB, for the reason that no address fits, when it
  gives none. Turning an integer back into a pointer gives the pointer and
  memories that
  {ref "The-fir-specification--Memory--Address-resolvers"}[turning it back]
  gives, and never fails.

*Definition: a translation through the layer.* A monad morphism
$`\varphi` from $`m` to $`n` gives one from the state layer over $`m` to
the state layer over $`n`: it translates each computation at each state,
$`x \mapsto (S \mapsto \varphi(x(S)))`.
:::

:::readable Fir.instDialectExtCallStateT Fir.extCall_stateT_setM Fir.extCall_stateT_setM_eq (pin := Fir.extCallUB) (fingerprint := "3121533852965512441")
*Definition: the external-call rule in the state layer.* In the state
layer over a way of computing, the external-call rule is the rule there,
lifted: it neither reads nor changes the state.

*Theorems.* So, over the set monad, an external call from any state $`S`
ends in UB, and only so, for the reason that an external call has no
meaning without a world: the layer with memory has no world either.
:::

:::readable Fir.MonadMorphism.state_mapsFrame Fir.MonadMorphism.state_choose Fir.MonadMorphism.state_chooseNaN Fir.MonadMorphism.state_ub (fingerprint := "12073770933935650719")
*Theorem: a translation through the layer keeps its effects.* It keeps
frames, since a frame of the layer is built from the monad's own steps.
It keeps a choice of $`w` bits when $`\varphi` keeps it, a NaN choice
when $`\varphi` keeps that, and UB when $`\varphi` keeps UB.
:::

:::readable Fir.MonadMorphism.state_keeps (pin := Fir.MonadMorphism.KeepsChoiceUB) (fingerprint := "15950878119703196822")
*Theorem: a translation that keeps choice and UB keeps them through the
layer.* When $`\varphi` keeps choice and UB, so does its translation
through the layer, by the two theorems above.
:::

:::readable Fir.MonadMorphism.state_alloc Fir.MonadMorphism.state_fromAddr Fir.MonadMorphism.state_free Fir.MonadMorphism.state_load Fir.MonadMorphism.state_store Fir.MonadMorphism.state_expose (fingerprint := "5880945281157506357")
*Theorem: a translation through the layer keeps the memory effect.* It
keeps allocating, turning an integer back into a pointer and freeing,
which end at once with a value. It keeps
loads, stores and exposures when $`\varphi` keeps UB, since each either
ends at once with a value or is UB.
:::

:::readable Fir.ChoiceTree.toSetState Fir.Func.run_toSetState (fingerprint := "13015231470910136122")
*Definition: the set of a tree, with memory.* The
{ref "The-fir-specification--Execution--Choice-trees"}[set of a tree],
$`\mathrm{set}`, translated through the layer, maps the state layer over
the tree of choices to the state layer over the set monad. It keeps
frames, and, by the
{ref "The-fir-specification--Execution--Monad-morphisms"}[interpreter's morphism theorem],
the run of a function in the layer over the tree has, at each state, the
run in the layer over the set monad as its set, when each op's semantics
in the one has its semantics in the other as its set. An external call is
UB in both layers, so the set keeps it.
:::

:::readable Fir.ChoiceTree.toSetState_keeps (fingerprint := "11139396066526368901")
*Theorem: the set of a tree keeps choice and UB through the layer.* The
set of a tree, translated through the layer, keeps choice and UB, since
$`\mathrm{set}` keeps them.
:::

:::readable Fir.ChoiceTree.toSetState_mapsExtCall (fingerprint := "6787513782530744460")
*Theorem.* The set of a tree, translated through the layer, keeps the
external-call rule: UB in the layer over the tree is UB in the layer over
the set monad.
:::
