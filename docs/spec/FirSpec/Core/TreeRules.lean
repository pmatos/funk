import VersoManual
import Fir.Core.TreeRules
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core dialect in the tree of
choices, which renders `Fir.Core.TreeRules` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "The core dialect in the tree of choices: readable blocks" =>

:::moduleDocs (fingerprint := "4527851466756114154")
:::

:::readable Fir.Core.mapsDenote (pin := Fir.MonadMorphism.MapsDenote) (pin := Fir.instDialectDenoteCoreDialectSetM) (pin := Fir.Core.instDialectDenoteCoreDialectChoiceTreeOp) (pin := Fir.Core.denoteIn) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.Op.exit?) (fingerprint := "16426023879755934800")
*Definition: the core ops in the tree of choices.* `fir-ref run` runs the
core dialect in the
{ref "The-fir-specification--Execution--Choice-trees"}[tree of choices].
There, each core op runs its
{ref "The-fir-specification--Execution--Core-op-semantics"}[rule], the
same rule, written once for any monad, that the set monad's semantics
runs. Where an op has no rule, as $`\mathsf{call}` has none, since its
meaning is its callee's run, the tree ends the path with
$`\mathsf{no\_outcome}~p`, naming the op $`p`, as the set monad gives it
no way to end (`docs/decisions/fir-ref.md#an-op-without-rules`).
`fir-ref` reports such a path as an error.

*Theorem: every core op has the same meaning in both monads.* For every
core op $`p` and operand vector $`\vec{v}`, the set of
$`\mathrm{denote}^{\mathrm{tree}}_p(\vec{v})` is
$`\mathrm{denote}^{\mathrm{set}}_p(\vec{v})`, and the set of
$`\mathrm{exit}^{\mathrm{tree}}_p(\vec{v})` is
$`\mathrm{exit}^{\mathrm{set}}_p(\vec{v})`: the map from trees to their
sets {ref "The-fir-specification--Execution--Monad-morphisms"}[keeps the semantics]
of the core ops. It holds because the rules are written once for any
monad, and the set of a tree keeps choice and UB
({ref "The-fir-specification--Memory--The-core___s-rules-with-memory"}[the core's rules with memory]),
while $`\mathsf{no\_outcome}~p` has no way to end.

This is the hypothesis of every theorem about the modes in the
{ref "The-fir-specification--Execution--Exhaustive___-scripted-and-sampled-modes"}[section on modes],
discharged once for the core dialect. So the theorems of the core's modes
hold for every core function, on every argument vector, at every fuel
budget.
:::

:::readable Fir.Core.memTreeDenote Fir.Core.memMapsDenote (pin := Fir.Core.memDenoteIn) (pin := Fir.MemMapsDenote) (fingerprint := "209049752458271192")
*Definition: the core ops in the tree of choices, with memory.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the tree of choices, where the run's memories have the layout entries
$`\ell` and the run names the core's memories by $`\rho`, each core op
runs by its
{ref "The-fir-specification--Memory--The-core___s-rules-with-memory"}[rule with memory],
as in the core's semantics with memory in the layer over the set monad;
an op with no rule ends its path with $`\mathsf{no\_outcome}~p`.

*Theorem: every core op has the same meaning with memory in both monads.*
At every naming $`\rho` of the core's memories and all layout entries
$`\ell` of the run's memories, the core's semantics in the layer over the
tree
{ref "The-fir-specification--Memory--Modes-with-memory"}[denotes] its
semantics with memory at $`\ell` and $`\rho`: the set of a tree, translated
through the layer, keeps choice and UB, so it maps each core op's rule
with memory in the one layer to its rule with memory in the other, op by
op.
:::

:::readable Fir.Core.memTree_liftState (pin := Fir.MonadMorphism.liftState) (fingerprint := "17260711733354945604")
*Theorem: no core op touches memory in the tree either.* At every layout
and naming, lifting a tree into the state layer maps each core op's
meaning in the tree to its meaning with memory in the layer over the tree:
lifting keeps choice and UB, and a path with no outcome stays one. So the
tree of a core run with memory is the tree of its run with no memory, as
the
{ref "The-fir-specification--Memory--The-core-dialect___s-modes"}[core's modes]
use.
:::
