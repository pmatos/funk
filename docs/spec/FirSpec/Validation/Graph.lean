import VersoManual
import Fir.Validation.Graph
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on reachability and dominance, decided,
which renders `Fir.Validation.Graph` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Reachability and dominance, decided: readable blocks" =>

:::moduleDocs (fingerprint := "5898655786998477867")
:::

:::readable Fir.Func.graph Fir.Func.start (pin := Fir.Block.succLabels) (pin := Fir.Func.entryLabel?) (pin := Fir.grouped) (fingerprint := "13429173844377504314")
*Definition: a function's graph as a table, and where its paths start.*
$`\mathrm{graph}(f)` is the hash table that gives the label of each block
$`b` of $`\mathrm{blocks}(f)` the labels $`\mathrm{targets}(b)` that $`b`
can jump to. It is built with
{ref "The-fir-specification--Validation--Tables"}[every value of each key],
so a label that names several blocks has the targets of each.
$`\mathrm{start}(f)` is the list that holds the label of the entry block,
or the empty list when the function has no block.
:::

:::readable Fir.reachedIn Fir.avoidingIn Fir.dominatesIn (fingerprint := "4402860240938784706")
*Definition: reachability and dominance, by search.* For a graph $`g`, a
list $`S` of start labels and labels $`a` and $`l`:

* $`\mathrm{reached}(g, S)` is what the
  {ref "The-fir-specification--Validation--Searching-a-graph"}[search]
  from $`S` finds, with nothing seen and every node allowed;
* $`\mathrm{avoiding}(g, S, a)` is what it finds when it may enter every
  node but $`a`;
* $`\mathrm{dominates}(g, S, a, l)` is true when $`a = l`, or when
  $`l` is not in $`\mathrm{avoiding}(g, S, a)`.

$$`\begin{aligned} & \mathrm{dominates}(g, S, a, l) \\ \iff\ & a = l \;\vee\; l \notin \mathrm{avoiding}(g, S, a) \end{aligned}`

These mirror the definitions of
{ref "The-fir-specification--Validation--Dominance"}[reachability and dominance]
one for one, with a search in place of "some path".
:::

:::readable Fir.Func.contains_graph Fir.Func.mem_graph (fingerprint := "17029759874086376305")
*Theorems: the table holds the function's blocks and edges.* For every
function $`f` and labels $`l`, $`x` and $`y`:

* $`l` is a key of $`\mathrm{graph}(f)` exactly when some block of
  $`\mathrm{blocks}(f)` has the label $`l`;
* $`y` is in $`\mathrm{graph}(f)[x]^*` exactly when the graph of $`f` has
  the edge $`x \to_f y`.

Here $`\mathrm{graph}(f)[x]^*` is the labels that the table gives $`x`, or
the empty list when $`x` is not a key.
:::

:::readable Fir.Func.reachable_iff_reach Fir.Func.reachesAvoiding_iff_reach (fingerprint := "17813624130479628169")
*Theorems: reachability, around a block or not, is reachability in the
table.* For every function $`f` and labels $`a` and $`l`, with
$`\mathrm{reach}` following the edges of the table,
$`\mathrm{next}(x) = \mathrm{graph}(f)[x]^*`:

$$`\begin{aligned} & \mathrm{reachable}_f(l) \\ \iff\ & \mathrm{reach}_{\top}(\mathrm{start}(f), l) \end{aligned}`

$$`\begin{aligned} & \mathrm{reachable}_{f \setminus a}(l) \\ \iff\ & \mathrm{reach}_{\neq a}(\mathrm{start}(f), l) \end{aligned}`

The subscript of $`\mathrm{reach}` is its test $`\mathrm{ok}`: $`\top`
allows every node, and $`{\neq a}` allows every node but $`a`.

They move each question about the function's paths into a question that
the search answers.
:::

:::readable Fir.Func.reachedIn_iff (fingerprint := "13064505560473412720")
*Theorem: the search decides which blocks the entry reaches.* For every
function $`f` and every label $`l` of a block of $`\mathrm{blocks}(f)`,
the search from the entry finds $`l` exactly when $`l` is reachable:

$$`\begin{aligned} & l \in \mathrm{reached}(\mathrm{graph}(f), \mathrm{start}(f)) \\ \iff\ & \mathrm{reachable}_f(l) \end{aligned}`

The check reports a block that the search does not find as unreachable,
and this theorem says it is right to.
:::

:::readable Fir.Func.dominatesIn_iff (fingerprint := "16231211915470369918")
*Theorem: the search decides dominance between the blocks of a function.*
For every function $`f`, every label $`a` and every label $`l` of a block
of $`\mathrm{blocks}(f)`:

$$`\begin{aligned} & \mathrm{dominates}(\mathrm{graph}(f), \mathrm{start}(f), a, l) \\ \iff\ & a \mathrel{\mathrm{dom}_f} l \end{aligned}`

The check of scope asks this of every use whose definition is in another
block.
:::
