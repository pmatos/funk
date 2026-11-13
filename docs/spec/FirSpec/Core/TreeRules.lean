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

:::moduleDocs (fingerprint := "18250013868975859619")
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
