import VersoManual
import Fir.Execution.Modes
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on exhaustive, scripted and sampled
modes, which renders `Fir.Execution.Modes` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "Exhaustive, scripted and sampled modes: readable blocks" =>

:::moduleDocs (fingerprint := "9913397997117995999")
:::

:::readable Fir.ChoiceTree.Leaf Fir.ChoiceTree.Leaf.ev? (fingerprint := "18031745832792441965")
*Definition: a leaf, and the way to end it stands for.* A walk of a
{ref "The-fir-specification--Execution--Choice-trees"}[tree of choices]
reports, for each path it follows, the leaf it reaches:

```grammar Fir.ChoiceTree.Leaf
\mathit{leaf}
ok          \mathsf{ok}~a
ub          \mathsf{ub}~\mathit{reason}
noOutcome   \mathsf{no\_outcome}~e
```

A leaf $`\ell` with an outcome stands for a way to end of the
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[set monad],
$`\mathrm{end}(\ell)`: the leaf $`\mathsf{ok}~a` stands for the way to
end $`\mathsf{ok}~a`, and the leaf $`\mathsf{ub}~r` for the way to end
$`\mathsf{ub}~r`. A leaf $`\mathsf{no\_outcome}~e`
stands for none.
:::

:::readable Fir.ChoiceTree.allBits Fir.ChoiceTree.mem_allBits (fingerprint := "5805791631794243625")
*Definition: every vector of $`w` bits, in order.* $`\mathrm{bits}(w)` is
the list of the $`2^w` vectors of $`w` bits, from the one that reads as
$`0` up to the one that reads as $`2^w - 1`, as unsigned numbers.

*Theorem: the list holds every vector.* Every vector of $`w` bits is in
$`\mathrm{bits}(w)`, so a walk that follows each of them misses no
subtree.
:::

:::readable Fir.ChoiceTree.collect Fir.ChoiceTree.collect_mem Fir.ChoiceTree.collect_some (fingerprint := "13934233481898007141")
*Definition and theorems: joining the lists of each element.* A helper of
exhaustive mode. For a function $`g` that gives each element a list, or
fails, $`\mathrm{collect}_g(\mathit{xs}, \mathit{acc})` gives the
starting list $`\mathit{acc}` reversed, then, in order, the lists that
$`g` gives each element of the list $`\mathit{xs}`, and fails when $`g`
fails on one. It keeps its work in the accumulator $`\mathit{acc}`, so a
long list costs no stack; exhaustive mode starts it from the empty list.
The theorems say that what it gives holds exactly the members of
$`\mathit{acc}` and of the lists $`g` gives, and that it gives something
only when $`g` gives a list for every element.
:::

:::readable Fir.ChoiceTree.explore (fingerprint := "9497081801497781709")
*Definition: exhaustive mode.* $`\mathrm{explore}(t, B)` lists every leaf
of the tree $`t`, each with the number of choices on its path, when no
path chooses more than $`B` bits in all, and fails otherwise:

$$`\begin{aligned} & \mathrm{explore}(\mathsf{pure}~a, B) = [(\mathsf{ok}~a, 0)] \\ & \mathrm{explore}(\mathsf{ub}~r, B) = [(\mathsf{ub}~r, 0)] \\ & \mathrm{explore}(\mathsf{no\_outcome}~e, B) \\ & \quad = [(\mathsf{no\_outcome}~e, 0)] \end{aligned}`

On a node $`\mathsf{choose}~w~(b \mapsto t_b)` with $`w \le B`, it
explores each subtree $`t_b` with the budget $`B - w`, for each $`b` of
$`\mathrm{bits}(w)` in order, adds one to each count, and joins the lists;
it fails if one of them fails. With $`w > B` it fails.

The number of paths doubles with each bit chosen, so the budget $`B`
bounds the work. Failing tells the user that the run chose more bits than
the budget allows, instead of an incomplete list.
:::

:::readable Fir.ChoiceTree.explore_toSet (fingerprint := "3967294515017348408")
*Theorem: within its budget, exhaustive mode finds exactly the tree's
set.* For every tree $`t` and budget $`B`, if $`\mathrm{explore}(t, B)`
gives the list $`L`, then for every way $`e` to end,

$$`e \in \mathrm{set}(t) \iff \exists (\ell, c) \in L.\ \mathrm{end}(\ell) = e`

Each way the tree may end is a leaf in the list, and each leaf in the
list that has an outcome is a way the tree may end.
:::

:::readable Fir.ChoiceTree.Within Fir.ChoiceTree.collect_isSome Fir.ChoiceTree.explore_isSome_iff (fingerprint := "16758010152506654825")
*Definition: within a budget.* A tree is _within_ the budget $`B` when no
path of it chooses more than $`B` bits in all: a leaf always is, and
$`\mathsf{choose}~w~(b \mapsto t_b)` is when $`w \le B` and every $`t_b`
is within $`B - w`.

*Theorem: exhaustive mode fails only when it must.* For every tree $`t`
and budget $`B`, $`\mathrm{explore}(t, B)` gives a list exactly when $`t`
is within $`B`. A step of the proof says when the helper that joins the
lists gives one: exactly when every element has one.
:::

:::readable Fir.ChoiceTree.Misfit (fingerprint := "8567880396582982358")
*Definition: why a choice sequence does not fit a run.* A _choice
sequence_ gives one value for each choice that a run makes, in order. It
_fits_ when it has exactly as many values as the run makes choices, and
each value reads as a value of its choice's width; on a path that ends
with no outcome, values left over are ignored, as scripted mode below
shows. Choices are counted from zero. A sequence that does not fit is an error of its own, a
_misfit_, and never an outcome:

```grammar Fir.ChoiceTree.Misfit
\mathit{misfit}
short    \mathsf{short}~\mathit{made}~w
unread   \mathsf{unread}~\mathit{made}~w~s
long     \mathsf{long}~\mathit{made}~\mathit{length}
```

* $`\mathsf{short}`: the run makes choice $`\mathit{made}`, of $`w` bits,
  and the sequence has no more values.
* $`\mathsf{unread}`: the value $`s` that the sequence gives for choice
  $`\mathit{made}` does not read as $`w` bits.
* $`\mathsf{long}`: the run makes $`\mathit{made}` choices, and the
  sequence has $`\mathit{length}` values.
:::

:::readable Fir.ChoiceTree.script (fingerprint := "10335797491189602108")
*Definition: scripted mode.* $`\mathrm{script}(t, \mathit{cs}, n)` follows
the path of the tree $`t` that the choice sequence $`\mathit{cs}` names,
after $`n` choices already made, and gives the leaf it reaches with the
number of choices made, or a misfit. A function $`\mathrm{read}(w, s)`,
which it takes as a parameter, reads the value $`s` as $`w` bits, or does
not. Here $`[]` is the empty sequence, $`s :: \mathit{cs}` is the
sequence whose first value is $`s`, followed by $`\mathit{cs}`, and
$`|\mathit{cs}|` is the length of $`\mathit{cs}`. On a leaf, and on a
node $`t = \mathsf{choose}~w~(b \mapsto t_b)` whose first value reads:

$$`\begin{aligned} & \mathrm{script}(\mathsf{no\_outcome}~e, \mathit{cs}, n) \\ & \quad = (\mathsf{no\_outcome}~e, n) \\ & \mathrm{script}(\mathsf{pure}~a, [], n) = (\mathsf{ok}~a, n) \\ & \mathrm{script}(\mathsf{ub}~r, [], n) = (\mathsf{ub}~r, n) \\ & \mathrm{script}(t, s :: \mathit{cs}, n) \\ & \quad = \mathrm{script}(t_b, \mathit{cs}, n + 1) \\ & \qquad \text{when } \mathrm{read}(w, s) = b \end{aligned}`

So a path with no outcome ends whatever is left of $`\mathit{cs}`. In
every other case it gives a misfit:

* At $`\mathsf{pure}~a` or $`\mathsf{ub}~r` with $`\mathit{cs}` not
  empty, $`\mathsf{long}~n~(n + |\mathit{cs}|)`.
* At $`t` with $`\mathit{cs}` empty, $`\mathsf{short}~n~w`.
* At $`t` with $`s :: \mathit{cs}` where $`\mathrm{read}(w, s)` does not
  read, $`\mathsf{unread}~n~w~s`.
:::

:::readable Fir.ChoiceTree.script_toSet (fingerprint := "14008406745184919625")
*Theorem: on a sequence that fits, scripted mode ends with a way the tree
may end.* For every $`\mathrm{read}`, tree $`t`, sequence $`\mathit{cs}`
and count $`n`: if $`\mathrm{script}(t, \mathit{cs}, n)` reaches the leaf
$`\ell` and $`\mathrm{end}(\ell) = e`, then $`e \in \mathrm{set}(t)`.
:::

:::readable Fir.ChoiceTree.Chosen Fir.ChoiceTree.readChosen (fingerprint := "6023394624286113321")
*Definition: a chosen value, and reading it back.* A value that a path
chose is a pair $`(u, b)` of a width $`u` and a vector $`b` of $`u` bits.
Read as $`w` bits, it gives $`b` when $`u = w`, and does not read
otherwise.
:::

:::readable Fir.ChoiceTree.sample (fingerprint := "8300353194910159562")
*Definition: sampled mode.* $`\mathrm{sample}(t, g)` follows one path of
the tree $`t`, drawing each choice as the path reaches it, and gives the
leaf it reaches with the values it chose, in order. A function
$`\mathrm{draw}(w, g)`, which it takes as a parameter, gives $`w` bits and
the next state of the generator $`g`. At a leaf it ends with no values,
and at a node $`t = \mathsf{choose}~w~(b \mapsto t_b)` it draws $`w` bits
and puts them before the values that the rest of the path chose:

$$`\begin{aligned} & \mathrm{sample}(\mathsf{pure}~a, g) = (\mathsf{ok}~a, []) \\ & \mathrm{sample}(\mathsf{ub}~r, g) = (\mathsf{ub}~r, []) \\ & \mathrm{sample}(\mathsf{no\_outcome}~e, g) \\ & \quad = (\mathsf{no\_outcome}~e, []) \\ & \mathrm{sample}(t, g) = (\ell, (w, b) :: \mathit{cs}) \end{aligned}`

where $`(b, g') = \mathrm{draw}(w, g)` and
$`(\ell, \mathit{cs}) = \mathrm{sample}(t_b, g')`.
:::

:::readable Fir.ChoiceTree.sample_script (fingerprint := "3654315093681788309")
*Theorem: the values that sampled mode chose fit the tree.* For every
$`\mathrm{draw}`, tree $`t`, generator $`g` and count $`n`, let
$`\mathrm{sample}(t, g)` give the leaf $`\ell` and the values
$`\mathit{cs}`. Then scripted mode on $`\mathit{cs}`, reading chosen
values as above, reaches the same leaf after $`n + |\mathit{cs}|`
choices:

$$`\mathrm{script}(t, \mathit{cs}, n) = (\ell,\ n + |\mathit{cs}|)`

So the values that sampled mode reports replay its run in scripted mode,
and sampled mode inherits scripted mode's theorems, whatever the
generator.
:::

:::readable Fir.PathEnd Fir.ChoiceTree.Leaf.pathEnd (fingerprint := "17367886164374681669")
*Definition: how a path of a run ends.* A path of a run of the
interpreter ends with an
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[outcome],
stuck, or with no outcome:

```grammar Fir.PathEnd
\mathit{path\_end}
outcome     \mathsf{outcome}~o
stuck       \mathsf{stuck}~s
noOutcome   \mathsf{no\_outcome}~e
```

A leaf of a run's tree holds a return, a run out of fuel or a stuck path,
or is UB or has no outcome. $`\mathrm{path\_end}(\ell)` reads it so: a
return $`\mathsf{ret}~o`, running out of fuel, and UB $`\mathsf{ub}~r` are
the outcomes $`\mathsf{ret}~o`, $`\mathsf{fuel\_exhausted}` and
$`\mathsf{ub}~r`; a stuck path is $`\mathsf{stuck}~s`; and
$`\mathsf{no\_outcome}~e` stays so. `fir-ref` reports each path this way.
:::

:::readable Fir.Outcome.ev Fir.Run.outcomes_iff Fir.ChoiceTree.Leaf.ev?_eq_outcome Fir.ChoiceTree.Leaf.ev?_eq_stuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (fingerprint := "8005299404318340067")
*Definition and theorems: outcomes as ways to end.* Steps in the proofs
below. Each outcome $`o` is a way a run's computation may end,
$`\mathrm{ev}(o)`, and $`o` is an outcome of a run $`R` exactly when
$`\mathrm{ev}(o) \in R`. A leaf stands for $`\mathrm{ev}(o)` exactly when
its path end is $`\mathsf{outcome}~o`, and it stands for the way to end
$`\mathsf{stuck}~s`, for some $`s`, exactly when its path end is
$`\mathsf{stuck}~s` for some $`s`.
:::

:::readable Fir.Func.run_toSet (fingerprint := "218765301515875500")
*Theorem: a run in the tree of choices has the run in the set monad as
its set.* Take any dialect, with what the
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter]
needs of it, and with a semantics of its ops both in trees and in the set
monad, such that the set of each op's semantics in trees is its semantics
in the set monad. Then for every module $`M`, function $`f`, arguments
$`\vec{v}` of $`f`'s parameter types and fuel $`k`, the set of the run of
$`f` in trees is the run of $`f` in the set monad:

$$`\mathrm{set}(\mathrm{run}^{\mathrm{tree}}_{M,f}(\vec{v}, k)) = \mathrm{run}^{\mathrm{set}}_{M,f}(\vec{v}, k)`

This is the theorem of the
{ref "The-fir-specification--Execution--Monad-morphisms"}[section on monad morphisms]
for the morphism from trees to sets.
:::

:::readable Fir.Func.explore_outcomes Fir.Func.explore_stuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (fingerprint := "3512900382591629054")
*Theorem: exhaustive mode gives exactly the outcomes of a run.* With the
dialect and the hypothesis of the previous theorem, let $`R_k` be the run
of $`f` in the set monad at fuel $`k`, and let exhaustive mode on the run's
tree, with the choice budget $`B`, give the list $`L`. Then for every
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[outcome] $`o`,

$$`\begin{aligned} & o \in \mathrm{out}(R_k) \iff \\ & \quad \exists (\ell, c) \in L.\ \mathrm{path\_end}(\ell) = \mathsf{outcome}~o \end{aligned}`

*Theorem: exhaustive mode finds a stuck path exactly when there is one.*
With the same hypotheses, $`R_k` is stuck exactly when some leaf of $`L`
has the path end $`\mathsf{stuck}~s`, for some $`s`.

The fuel budget and the choice budget are different budgets: the theorems
speak of the run at one fuel budget, as the section on
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[outcomes and behaviours]
explains.
:::

:::readable Fir.Func.script_outcomes Fir.Func.script_stuck (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (fingerprint := "17647192191096139031")
*Theorem: on a sequence that fits, scripted mode gives an outcome of a
run.* With the dialect and the hypothesis of the theorems above, let
scripted mode on the run's tree, with any $`\mathrm{read}` and choice
sequence $`\mathit{cs}`, starting from no choices made, reach the leaf
$`\ell`, with no misfit. If
$`\mathrm{path\_end}(\ell) = \mathsf{outcome}~o`, then
$`o \in \mathrm{out}(R_k)`.

*Theorem: scripted mode finds a stuck path only when there is one.* With
the same hypotheses, if $`\mathrm{path\_end}(\ell) = \mathsf{stuck}~s`, then
$`R_k` is stuck.
:::
