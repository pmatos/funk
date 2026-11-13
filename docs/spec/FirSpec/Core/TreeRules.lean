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

:::moduleDocs (fingerprint := "17003934263112107456")
:::

:::readable Fir.Core.freezeValue_toSet (pin := Fir.Core.instDialectDenoteCoreDialectChoiceTreeOp) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.Op.exit?) (pin := Fir.Core.freezeValue) (fingerprint := "7156130758232906077")
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

*Theorem: $`\mathsf{freeze}`'s rule has the same meaning in both monads.*
For every set $`E` of reasons, width $`w` and
$`a \in \llbracket \mathsf{i}w \rrbracket`, the set of the tree that
$`\mathsf{freeze}`'s rule builds on $`a` is the computation that the rule
gives on $`a` in the set monad: $`a` itself, or, for poison, every vector
of $`w` bits.
:::

:::readable Fir.Core.ruleOfEv_toSet Fir.Core.exitOfEv_toSet (pin := Fir.Core.ruleOfEv) (pin := Fir.Core.exitOfEv) (fingerprint := "8629023250347109559")
*Theorem: the rules made from a way to end have the same meaning in both
monads.* For every set $`E` of reasons, a
{ref "The-fir-specification--Execution--Division-rules"}[division rule]
made from a function $`g` to a way to end has, on every two operands of
$`\mathsf{i}w`, the set monad's computation as the set of its tree. So
does a {ref "The-fir-specification--Execution--Branch-rules"}[terminator rule]
made from a way to end, such as $`\mathsf{cond\_br}`'s or
$`\mathsf{unreachable}`'s. Both end in one
way and never choose, so their trees are single leaves.
:::

:::readable Fir.Core.mapsDenote (pin := Fir.MonadMorphism.MapsDenote) (pin := Fir.Core.instDialectDenoteCoreDialectChoiceTreeOp) (pin := Fir.instDialectDenoteCoreDialectSetM) (fingerprint := "7901270225191683949")
*Theorem: every core op has the same meaning in both monads.* For every
core op $`p` and operand vector $`\vec{v}`, the set of
$`\mathrm{denote}^{\mathrm{tree}}_p(\vec{v})` is
$`\mathrm{denote}^{\mathrm{set}}_p(\vec{v})`, and the set of
$`\mathrm{exit}^{\mathrm{tree}}_p(\vec{v})` is
$`\mathrm{exit}^{\mathrm{set}}_p(\vec{v})`: the map from trees to their
sets {ref "The-fir-specification--Execution--Monad-morphisms"}[keeps the semantics]
of the core ops.

This is the hypothesis of every theorem about the modes in the
{ref "The-fir-specification--Execution--Exhaustive___-scripted-and-sampled-modes"}[section on modes],
discharged once for the core dialect. It holds because the rules are
written once for any monad, and the set of a tree keeps its steps, its
choices and its UB. So the theorems of the core's modes hold for every core function,
on every argument vector, at every fuel budget.
:::

:::readable Fir.Core.memTreeDenote Fir.Core.memMapsDenote (pin := Fir.DialectDenote.liftState) (pin := Fir.MemMapsDenote) (fingerprint := "11987007576216303939")
*Definition: the core ops in the tree of choices, with memory.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the tree of choices, where the run's memories have the layout entries
$`\ell` and the run names the core's memories by $`\rho`, each core op
runs by its rule in the tree and keeps the memories, as in the core's
{ref "The-fir-specification--Memory--Core-functions-with-memory"}[semantics with memory]
each op runs by its rule in the set monad and keeps the memories: no core
op touches memory yet.

*Theorem: every core op has the same meaning with memory in both monads.*
At every naming $`\rho` of the core's memories and all layout entries
$`\ell` of the run's memories, the core's semantics in the layer over the
tree
{ref "The-fir-specification--Memory--Modes-with-memory"}[denotes] its
semantics with memory at $`\ell` and $`\rho`: the set of a tree, translated through
the layer, keeps a lifted computation, and maps each core op's rule in the
tree to its rule in the set monad, by the theorem above.
:::
