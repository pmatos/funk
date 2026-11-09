import VersoManual
import Fir.Validation.Search
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on searching a graph, which renders
`Fir.Validation.Search` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Searching a graph: readable blocks" =>

:::moduleDocs (fingerprint := "12081133205208568887")
:::

:::readable Fir.length_filter_lt (fingerprint := "13639080189621108566")
*Theorem: a stricter filter keeps fewer elements.* Let $`p` and $`q` be two
tests on the elements of a list $`l`, such that every element that passes
$`q` passes $`p`. If some element $`x` of $`l` passes $`p` but not $`q`,
then fewer elements of $`l` pass $`q` than pass $`p`.

$$`\begin{aligned} & \bigl(\forall y.\ q(y) \implies p(y)\bigr) \\ \wedge\ & x \in l \wedge p(x) \wedge \neg q(x) \\ \implies & |l|_q < |l|_p \end{aligned}`

Here $`|l|_p` is the number of elements of $`l` that pass $`p`. The search
below uses it to show that it ends: marking a node seen lowers the number
of nodes not yet seen.
:::

:::readable Fir.Reach (fingerprint := "9836448204162335582")
*Definition: the nodes a path reaches.* Fix a graph, given by the
successors $`\mathrm{next}(x)` of each node $`x`, a test $`\mathrm{ok}` of
the nodes a path may enter, and a list $`S` of start nodes.
$`\mathrm{reach}(S, y)` holds when some path from a node of $`S`, following
edges and entering only nodes that pass $`\mathrm{ok}`, the first one
included, reaches $`y`. It is the least relation closed under these rules:

$$`\frac{x \in S \qquad \mathrm{ok}(x)}{\mathrm{reach}(S, x)}`

$$`\frac{\mathrm{reach}(S, x) \qquad y \in \mathrm{next}(x) \qquad \mathrm{ok}(y)}{\mathrm{reach}(S, y)}`

With $`\mathrm{ok}` always true it is
{ref "The-fir-specification--Validation--Dominance"}[reachability]; with
$`\mathrm{ok}(y)` true for every $`y \neq a` it is reachability around the
node $`a`. Where the test matters, $`\mathrm{reach}_{\mathrm{ok}}(S, y)`
names it.
:::

:::readable Fir.unseen Fir.unseen_insert_lt (fingerprint := "11856536830479484098")
*Definition and theorem: the nodes not yet seen.* For a graph given as a
hash table $`g` from each node to its successors, and a set $`\mathit{seen}`
of nodes, $`\mathrm{unseen}(g, \mathit{seen})` is the number of keys of
$`g` that are not in $`\mathit{seen}`.

*Theorem:* for nodes whose equality test agrees with equality, as the test
of labels does, if $`x` is a key of $`g` and is not in $`\mathit{seen}`, then
adding $`x` to $`\mathit{seen}` lowers the count:

$$`\mathrm{unseen}(g, \mathit{seen} \cup \{x\}) < \mathrm{unseen}(g, \mathit{seen})`

This is the measure that shows the search ends.
:::

:::readable Fir.search (fingerprint := "1329295632825354045")
*Definition: the search.* $`\mathrm{search}(g, \mathrm{ok}, \mathit{seen}, \mathit{work})`
takes a graph $`g` as a hash table, a test $`\mathrm{ok}`, a set
$`\mathit{seen}` of nodes and a list $`\mathit{work}` of nodes to visit. It
takes the nodes of $`\mathit{work}` in turn:

* when the node $`x` is a key of $`g`, passes $`\mathrm{ok}` and is not in
  $`\mathit{seen}`, it adds $`x` to $`\mathit{seen}` and puts the
  successors of $`x` in front of the rest of the work;
* otherwise it drops $`x`.

When no work is left, the result is $`\mathit{seen}`. Every step either
adds a node not yet seen, so that $`\mathrm{unseen}` falls, or shortens
the work with $`\mathrm{unseen}` unchanged, so the search ends on every
graph. It is a depth-first search that visits each node at most once. Like
the measure, it asks that the nodes' equality test agrees with equality, as
the test of labels does, and so does every theorem about it below.
Below, $`g[x]^*` is the successors that $`g` gives $`x`, or the empty list
when $`x` is not a key of $`g`.
:::

:::readable Fir.search_mono Fir.search_covers (fingerprint := "2643118911616308034")
*Theorems: the search keeps what it has seen, and sees every node of its
work that it may visit.* For nodes whose equality test agrees with
equality, and for every graph $`g`, test $`\mathrm{ok}`, set
$`\mathit{seen}` and list $`\mathit{work}`:

* every node $`z` of $`\mathit{seen}` is in the result;
* every node $`z` of $`\mathit{work}` that is a key of $`g` and passes
  $`\mathrm{ok}` is in the result.
:::

:::readable Fir.search_closed (fingerprint := "11967676191980749979")
*Theorem: the result is closed under the edges it may follow.* Call a set
$`R` _closed_ when, for every node $`x` of $`R` and every successor
$`y \in g[x]^*` that is a key of $`g` and passes $`\mathrm{ok}`, $`y` is in
$`R`. Let $`R` be the result of the search. If the successors of the nodes
of $`\mathit{seen}` that are keys and pass $`\mathrm{ok}` are all in $`R`,
then $`R` is closed.

Started with nothing seen, the premise holds trivially, so the result
holds every node that a path from it can reach: no path escapes it.
:::

:::readable Fir.search_sound (fingerprint := "4023362449948315129")
*Theorem: every node the search sees is reached.* Fix a list $`S` of start
nodes, and write $`\mathrm{reach}(S, y)` with $`\mathrm{next}(x) = g[x]^*`.
If $`\mathrm{reach}(S, x)` holds for every node $`x` of $`\mathit{seen}`,
and for every node $`x` of $`\mathit{work}` that passes $`\mathrm{ok}`, then
it holds for every node of the result.

So the search never finds a node that no path reaches.
:::

:::readable Fir.contains_search_iff (fingerprint := "14131843461188492695")
*Theorem: the search finds exactly the nodes that a path reaches.* For
nodes whose equality test agrees with equality, and for every graph $`g`, test $`\mathrm{ok}`, list $`S` of start nodes and key $`y` of
$`g`, the search from $`S` with nothing seen finds $`y` exactly when a path
reaches it:

$$`y \in \mathrm{search}(g, \mathrm{ok}, \emptyset, S) \iff \mathrm{reach}(S, y)`

Here $`\mathrm{reach}` follows the edges of $`g`: $`\mathrm{next}(x) = g[x]^*`.

The four theorems above give it: the search is sound, and what it finds is
closed and holds every start node it may visit. This is what lets the check
decide reachability and dominance, which speak of every path, by running
one search.
:::
