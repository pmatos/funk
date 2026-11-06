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

:::readable Fir.Core.freezeValue_toSet (pin := Fir.Core.instDialectDenoteCoreDialectChoiceTreeOp) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.Op.exit?) (pin := Fir.Core.freezeValue) (fingerprint := "17753302036347918519")
*Definition: the core ops in the tree of choices.* `fir-ref run` runs the
core dialect in the
{ref "The-fir-specification--Execution--Choice-trees"}[tree of choices].
There, each core op runs its
{ref "The-fir-specification--Execution--Core-op-semantics"}[rule], the
same rule, written once for any monad, that the set monad's semantics
runs. Where an op has no rule, as $`\mathsf{call}` has none, since its
meaning is its callee's run, the tree ends the path with
$`\mathsf{no\_outcome}~p`, naming the op $`p`, as the set monad gives it
no way to end (ADR-2026-10-30-1855).
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
made from a way to end, such as $`\mathsf{cond\_br}`'s. Both end in one
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
{ref "The-fir-specification--Execution--Exhaustive___-scripted-and-sampled-modes"}[previous section],
discharged once for the core dialect. It holds because the rules are
written once for any monad, and the set of a tree keeps its steps, its
choices and its UB. So the theorems below hold for every core function,
on every argument vector, at every fuel budget.
:::

:::readable Fir.Core.exhaustive Fir.Core.scripted (pin := Fir.ChoiceTree.explore) (pin := Fir.ChoiceTree.script) (fingerprint := "8824377896590504095")
*Definition: exhaustive and scripted mode on a core function.* For a core
function $`f` of a module $`M`, arguments $`\vec{v}` of its parameter
types and fuel $`k`:

* $`\mathrm{exhaustive}(M, f, \vec{v}, k, B)` is exhaustive mode, with the
  choice budget $`B`, on the tree of the run of $`f` on $`\vec{v}` with
  $`k` steps of fuel: every path's leaf and number of choices, or a failure
  when some path chooses more than $`B` bits in all.
* $`\mathrm{scripted}(M, f, \vec{v}, k, \mathit{cs})` is scripted mode on
  that tree, following the choice sequence $`\mathit{cs}`, each value read
  by a given $`\mathrm{read}`, from no choices made: the leaf it reaches
  and its number of choices, or why $`\mathit{cs}` does not fit.

`fir-ref` computes these, and sampled mode below, and nothing else, to
report a run.
:::

:::readable Fir.Core.exhaustive_outcomes Fir.Core.exhaustive_stuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "11836097572887930469")
*Theorem: exhaustive mode gives exactly the outcomes of a core run.* For
every module $`M`, function $`f`, arguments $`\vec{v}`, fuel $`k` and
choice budget $`B`, let $`R_k` be the run of $`f` on $`\vec{v}` in the
set monad, at fuel $`k`. If $`\mathrm{exhaustive}(M, f, \vec{v}, k, B)`
gives the list $`L`, then for every
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[outcome] $`o`,
with $`\mathrm{path\_end}` the
{ref "The-fir-specification--Execution--Exhaustive___-scripted-and-sampled-modes"}[path end]
of a leaf,

$$`\begin{aligned} & o \in \mathrm{out}(R_k) \iff \\ & \quad \exists (\ell, c) \in L.\ \mathrm{path\_end}(\ell) = \mathsf{outcome}~o \end{aligned}`

*Theorem: it lists a stuck path exactly when the run has one.* With the
same hypotheses, $`R_k` is stuck exactly when some leaf of $`L` has the
path end $`\mathsf{stuck}~s`, for some $`s`.
:::

:::readable Fir.Core.scripted_outcomes Fir.Core.scripted_stuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "10682984764488149608")
*Theorem: on a sequence that fits, scripted mode gives an outcome of a
core run.* For every $`\mathrm{read}`, module $`M`, function $`f`,
arguments $`\vec{v}`, fuel $`k` and choice sequence $`\mathit{cs}`, if
$`\mathrm{scripted}(M, f, \vec{v}, k, \mathit{cs})` reaches the leaf
$`\ell`, with no misfit, and $`\mathrm{path\_end}(\ell) = \mathsf{outcome}~o`,
then $`o \in \mathrm{out}(R_k)`.

*Theorem: it reports a stuck path only when the run has one.* With the
same hypotheses, if $`\mathrm{path\_end}(\ell) = \mathsf{stuck}~s`, then
$`R_k` is stuck.
:::

:::readable Fir.Core.sampled (pin := Fir.ChoiceTree.sample) (fingerprint := "16977139950284272472")
*Definition: sampled mode on a core function.* For a function
$`\mathrm{draw}` and a generator $`g`,
$`\mathrm{sampled}(M, f, \vec{v}, k, g)` is sampled mode on the tree of
the run of $`f` on $`\vec{v}` with $`k` steps of fuel: the leaf of the path
on which $`\mathrm{draw}` gives each choice, from $`g`, and the values
chosen on it, in order.
:::

:::readable Fir.Core.sampled_fits (pin := Fir.ChoiceTree.readChosen) (fingerprint := "6811916062769141243")
*Theorem: the values that sampled mode chose fit the run.* For every
$`\mathrm{draw}`, module $`M`, function $`f`, arguments $`\vec{v}`, fuel
$`k` and generator $`g`, let $`\mathrm{sampled}(M, f, \vec{v}, k, g)`
give the leaf $`\ell` and the values $`\mathit{cs}`. Then scripted mode on
$`\mathit{cs}`, reading chosen values back, reaches $`\ell` after
$`|\mathit{cs}|` choices, the length of $`\mathit{cs}`:

$$`\mathrm{scripted}(M, f, \vec{v}, k, \mathit{cs}) = (\ell,\ |\mathit{cs}|)`

So a sampled run can be replayed exactly, from the values `fir-ref`
reports.
:::

:::readable Fir.Core.sampled_outcomes Fir.Core.sampled_stuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "8499175868464204258")
*Theorem: sampled mode gives an outcome of a core run, whatever the
generator.* For every $`\mathrm{draw}`, module $`M`, function $`f`,
arguments $`\vec{v}`, fuel $`k` and generator $`g`, if the leaf $`\ell`
that $`\mathrm{sampled}(M, f, \vec{v}, k, g)` gives has
$`\mathrm{path\_end}(\ell) = \mathsf{outcome}~o`, then
$`o \in \mathrm{out}(R_k)`.

*Theorem: it reports a stuck path only when the run has one.* With the
same hypotheses, if $`\mathrm{path\_end}(\ell) = \mathsf{stuck}~s`, then
$`R_k` is stuck. Both follow from scripted mode's theorems, since the
values sampled mode chose fit the run.
:::
