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

:::moduleDocs (fingerprint := "11414522726157933595")
:::

:::readable Fir.Core.freezeValue_toSet (pin := Fir.Core.instDialectDenoteCoreDialectChoiceTreeOp) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.Op.exit?) (pin := Fir.Core.freezeValue) (fingerprint := "18105441842968644650")
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
choices and its UB. So the theorems below hold for every core function,
on every argument vector, at every fuel budget.
:::

:::readable Fir.Core.memMapsDenote (pin := Fir.Core.instDialectDenoteCoreDialectStateTMemoriesChoiceTreeOp) (pin := Fir.DialectDenote.liftState) (pin := Fir.MemMapsDenote) (fingerprint := "11424595781705454996")
*Definition: the core ops in the tree of choices, with memory.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the tree of choices, each core op runs by its rule in the tree and keeps
the memories, as in the core's
{ref "The-fir-specification--Memory--Core-functions-with-memory"}[semantics with memory]
each op runs by its rule in the set monad and keeps the memories: no core
op touches memory yet.

*Theorem: every core op has the same meaning with memory in both monads.*
At every naming $`\rho` of the core's memories and every unit width
$`u`, the core's semantics in the layer over the tree
{ref "The-fir-specification--Memory--Modes-with-memory"}[denotes] its
semantics with memory at $`\rho`: the set of a tree, translated through
the layer, keeps a lifted computation, and maps each core op's rule in the
tree to its rule in the set monad, by the theorem above.
:::

:::readable Fir.Core.exhaustive Fir.Core.scripted (pin := Fir.ChoiceTree.explore) (pin := Fir.ChoiceTree.script) (pin := Fir.Func.memTree) (fingerprint := "6469590226338190409")
*Definition: exhaustive and scripted mode on a core function.* For unit
widths $`u` of the run's memories, a core function $`f` of a module
$`M`, arguments $`\vec{v}` of its parameter types and fuel $`k`, let
$`T = \mathrm{tree}^{\mathrm{mem}}_{M,f}(\vec{v}, k)` be the
{ref "The-fir-specification--Memory--Modes-with-memory"}[tree of its run with memory],
from the empty memories:

* $`\mathrm{exhaustive}_u(M, f, \vec{v}, k, B)` is exhaustive mode, with
  the choice budget $`B`, on $`T`: every path's leaf and number of
  choices, or a failure when some path chooses more than $`B` bits in all.
* $`\mathrm{scripted}_u(M, f, \vec{v}, k, \mathit{cs})` is scripted mode
  on $`T`, following the choice sequence $`\mathit{cs}`, each value read
  by a given $`\mathrm{read}`, from no choices made: the leaf it reaches
  and its number of choices, or why $`\mathit{cs}` does not fit.

`fir-ref` computes these, and sampled mode below, and nothing else, to
report a run. It names the core's memories by themselves; the core has no
memory yet, so no unit width is needed until the module's data layout
gives them (`docs/decisions/fir-ref-memory.md#the-modes-run-with-memory`).
:::

:::readable Fir.Core.sampled (pin := Fir.ChoiceTree.sample) (fingerprint := "11139068504129417113")
*Definition: sampled mode on a core function.* For a function
$`\mathrm{draw}` and a generator $`g`,
$`\mathrm{sampled}_u(M, f, \vec{v}, k, g)` is sampled mode on the tree of
the run with memory of $`f` on $`\vec{v}` with $`k` steps of fuel: the
leaf of the path on which $`\mathrm{draw}` gives each choice, from
$`g`, and the values chosen on it, in order.
:::

:::readable Fir.Core.exhaustive_memOutcomes Fir.Core.exhaustive_memStuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "9482688737533896207")
*Theorem: exhaustive mode gives exactly the outcomes of a core run with
memory.* For every naming $`\rho` of the core's memories, unit widths
$`u`, module $`M`, function $`f`, arguments $`\vec{v}`, fuel $`k` and
choice budget $`B`, let $`R^\rho_k` be the
{ref "The-fir-specification--Memory--Runs-with-memory"}[run with memory]
of $`f` at $`\rho` on $`\vec{v}`, at fuel $`k`. If
$`\mathrm{exhaustive}_u(M, f, \vec{v}, k, B)` gives the list $`L`, then
for every {ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[outcome] $`o`,
with $`\mathrm{path\_end}` the
{ref "The-fir-specification--Execution--Exhaustive___-scripted-and-sampled-modes"}[path end]
of a leaf,

$$`\begin{aligned} & o \in \mathrm{out}(R^\rho_k) \iff \\ & \quad \exists (\ell, c) \in L.\ \mathrm{path\_end}(\ell) = \mathsf{outcome}~o \end{aligned}`

*Theorem: it lists a stuck path exactly when the run has one.* With the
same hypotheses, $`R^\rho_k` is stuck exactly when some leaf of $`L` has
the path end $`\mathsf{stuck}~s`, for some $`s`. Both are the
{ref "The-fir-specification--Memory--Modes-with-memory"}[theorems of modes with memory],
since the core's semantics in the tree denotes its semantics with memory.
:::

:::readable Fir.Core.scripted_memOutcomes Fir.Core.scripted_memStuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "3971839162030426189")
*Theorem: on a sequence that fits, scripted mode gives an outcome of a
core run with memory.* For every $`\rho`, $`u`, $`\mathrm{read}`,
module $`M`, function $`f`, arguments $`\vec{v}`, fuel $`k` and choice
sequence $`\mathit{cs}`, if
$`\mathrm{scripted}_u(M, f, \vec{v}, k, \mathit{cs})` reaches the leaf
$`\ell`, with no misfit, and
$`\mathrm{path\_end}(\ell) = \mathsf{outcome}~o`, then
$`o \in \mathrm{out}(R^\rho_k)`.

*Theorem: it reports a stuck path only when the run has one.* With the
same hypotheses, if $`\mathrm{path\_end}(\ell) = \mathsf{stuck}~s`,
then $`R^\rho_k` is stuck.
:::

:::readable Fir.Core.sampled_fits (pin := Fir.ChoiceTree.readChosen) (fingerprint := "2672261356596035902")
*Theorem: the values that sampled mode chose fit the run.* For every
$`u`, $`\mathrm{draw}`, module $`M`, function $`f`, arguments
$`\vec{v}`, fuel $`k` and generator $`g`, let
$`\mathrm{sampled}_u(M, f, \vec{v}, k, g)` give the leaf $`\ell` and the
values $`\mathit{cs}`. Then scripted mode on $`\mathit{cs}`, reading
chosen values back, reaches $`\ell` after $`|\mathit{cs}|` choices, the
length of $`\mathit{cs}`:

$$`\mathrm{scripted}_u(M, f, \vec{v}, k, \mathit{cs}) = (\ell,\ |\mathit{cs}|)`

So a sampled run can be replayed exactly, from the values `fir-ref`
reports.
:::

:::readable Fir.Core.sampled_memOutcomes Fir.Core.sampled_memStuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "10867089033334170208")
*Theorem: sampled mode gives an outcome of a core run with memory,
whatever the generator.* For every $`\rho`, $`u`, $`\mathrm{draw}`,
module $`M`, function $`f`, arguments $`\vec{v}`, fuel $`k` and generator
$`g`, if the leaf $`\ell` that $`\mathrm{sampled}_u(M, f, \vec{v}, k, g)`
gives has $`\mathrm{path\_end}(\ell) = \mathsf{outcome}~o`, then
$`o \in \mathrm{out}(R^\rho_k)`.

*Theorem: it reports a stuck path only when the run has one.* With the
same hypotheses, if $`\mathrm{path\_end}(\ell) = \mathsf{stuck}~s`,
then $`R^\rho_k` is stuck. Both follow from scripted mode's theorems,
since the values sampled mode chose fit the run.
:::

:::readable Fir.Core.memTree_eq (pin := Fir.MonadMorphism.liftState) (fingerprint := "8011919765119740936")
*Theorem: the tree of a core run with memory is the tree of its run.* For
every unit widths $`u`, module $`M`, function $`f`, arguments $`\vec{v}`
and fuel $`k`, $`\mathrm{tree}^{\mathrm{mem}}_{M,f}(\vec{v}, k)` is the
tree of the run of $`f` on $`\vec{v}` with $`k` steps, with no memory:
the same paths, the same choices and the same leaves, in the same order.
Each core op keeps the memories, so the run in the layer is the run in the
tree, lifted, by the
{ref "The-fir-specification--Execution--Monad-morphisms"}[interpreter's morphism theorem],
and dropping the memories at each leaf gives the run in the tree back. So
every mode reports, path for path, what it reported before runs had
memory.
:::

:::readable Fir.Core.exhaustive_outcomes Fir.Core.exhaustive_stuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "2292959288162279249")
*Theorem: exhaustive mode gives exactly the outcomes of a core run.* For
every $`u`, module $`M`, function $`f`, arguments $`\vec{v}`, fuel $`k`
and choice budget $`B`, let $`R_k` be the run of $`f` on $`\vec{v}` in
the set monad, at fuel $`k`. If
$`\mathrm{exhaustive}_u(M, f, \vec{v}, k, B)` gives the list $`L`, then
for every outcome $`o`,

$$`\begin{aligned} & o \in \mathrm{out}(R_k) \iff \\ & \quad \exists (\ell, c) \in L.\ \mathrm{path\_end}(\ell) = \mathsf{outcome}~o \end{aligned}`

*Theorem: it lists a stuck path exactly when the run has one.* With the
same hypotheses, $`R_k` is stuck exactly when some leaf of $`L` has the
path end $`\mathsf{stuck}~s`, for some $`s`. Both are the
{ref "The-fir-specification--Execution--Exhaustive___-scripted-and-sampled-modes"}[theorems of the modes]
on the tree of the run, by the theorem above.
:::

:::readable Fir.Core.scripted_outcomes Fir.Core.scripted_stuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "17629814800224753611")
*Theorem: on a sequence that fits, scripted mode gives an outcome of a
core run.* For every $`u`, $`\mathrm{read}`, module $`M`, function
$`f`, arguments $`\vec{v}`, fuel $`k` and choice sequence
$`\mathit{cs}`, if $`\mathrm{scripted}_u(M, f, \vec{v}, k, \mathit{cs})`
reaches the leaf $`\ell`, with no misfit, and
$`\mathrm{path\_end}(\ell) = \mathsf{outcome}~o`, then
$`o \in \mathrm{out}(R_k)`.

*Theorem: it reports a stuck path only when the run has one.* With the
same hypotheses, if $`\mathrm{path\_end}(\ell) = \mathsf{stuck}~s`,
then $`R_k` is stuck.
:::

:::readable Fir.Core.sampled_outcomes Fir.Core.sampled_stuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "5516853520957676611")
*Theorem: sampled mode gives an outcome of a core run, whatever the
generator.* For every $`u`, $`\mathrm{draw}`, module $`M`, function
$`f`, arguments $`\vec{v}`, fuel $`k` and generator $`g`, if the leaf
$`\ell` that $`\mathrm{sampled}_u(M, f, \vec{v}, k, g)` gives has
$`\mathrm{path\_end}(\ell) = \mathsf{outcome}~o`, then
$`o \in \mathrm{out}(R_k)`.

*Theorem: it reports a stuck path only when the run has one.* With the
same hypotheses, if $`\mathrm{path\_end}(\ell) = \mathsf{stuck}~s`,
then $`R_k` is stuck. Both follow from scripted mode's theorems, since the
values sampled mode chose fit the run.
:::
