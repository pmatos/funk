import VersoManual
import Fir.Validation.Dominance
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on dominance, which renders
`Fir.Validation.Dominance` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Dominance: readable blocks" =>

:::readable Fir.Block.succLabels Fir.Func.Edge Fir.Func.entryLabel? (fingerprint := "14653745792150054030")
*Definition: the control-flow graph of a function.* The nodes of the graph
of a function $`f` are the labels of the blocks of
$`\mathrm{blocks}(f)`, its
{ref "The-fir-specification--Validation--Scope-and-symbols"}[top-level blocks].

* $`\mathrm{targets}(b)` is the labels of the successors of the ops of the
  block $`b`, in order: the blocks that $`b` can jump to. In a valid
  function only the last op of a block, its terminator, has successors.
* There is an edge $`a \to_f l` when some block $`b` of
  $`\mathrm{blocks}(f)` has the label $`a` and $`l` is in
  $`\mathrm{targets}(b)`.
* $`\mathrm{entry}(f)` is the label of the first block of
  $`\mathrm{blocks}(f)`, and is undefined when the body has no block.

Every path that the rules below speak of starts at $`\mathrm{entry}(f)`.
:::

:::readable Fir.Func.Reachable Fir.Func.ReachesAvoiding (fingerprint := "18057698545448609824")
*Definition: reachable blocks, and blocks reachable around a block.* The
label $`l` is _reachable_ in $`f`, written $`\mathrm{reachable}_f(l)`, when
some path through the graph goes from the entry to $`l`. It is the least
relation closed under two
{ref "The-fir-specification"}[inference rules], one for the start of a path
and one for each further edge.

$$`\frac{\mathrm{entry}(f) = e}{\mathrm{reachable}_f(e)}`

$$`\frac{\mathrm{reachable}_f(x) \qquad x \to_f y}{\mathrm{reachable}_f(y)}`

$`\mathrm{reachable}_{f \setminus a}(l)` says that some path goes from the
entry to $`l` without passing through the block labelled $`a`: it is
reachability in the graph of $`f` with $`a` removed, its two ends included.

$$`\frac{\mathrm{entry}(f) = e \qquad e \neq a}{\mathrm{reachable}_{f \setminus a}(e)}`

$$`\frac{\mathrm{reachable}_{f \setminus a}(x) \qquad x \to_f y \qquad y \neq a}{\mathrm{reachable}_{f \setminus a}(y)}`

The first relation gives the rule that every block is reachable, and the
second gives dominance, next.
:::

:::readable Fir.Func.Dominates (fingerprint := "5424848281276842892")
*Definition: dominance.* The block labelled $`a` _dominates_ the block
labelled $`l` in $`f`, written $`a \mathrel{\mathrm{dom}_f} l`, when they
are one block, or when no path from the entry reaches $`l` without passing
through $`a`.

$$`\begin{aligned} a \mathrel{\mathrm{dom}_f} l \iff\ & a = l \\ \vee\ & \neg\, \mathrm{reachable}_{f \setminus a}(l) \end{aligned}`

This is "every path from the entry to $`l` passes through $`a`", stated
as the absence of one kind of path rather than as a property of every
path. On a block that the entry does
not reach it would hold for every $`a`, which is why validation asks every
block to be reachable.
:::

:::readable Fir.DefSite (fingerprint := "14200321266705955909")
*Definition: definition sites.* A value is defined at one of three kinds of
site: as a parameter of the function, as an argument of the block labelled
$`l`, or as a result of the op at index $`j` of the block labelled $`l`,
counting the ops of a block from 0.

```grammar Fir.DefSite
\mathit{site}
param    \mathsf{param}
arg      \mathsf{arg}~l
result   \mathsf{result}~l~j
```
:::

:::readable Fir.Func.Defines (fingerprint := "1299138112129809087")
*Definition: where a function defines a value.* $`\mathrm{defines}_f(x, \mathit{site})`
holds when the function $`f` defines a value named $`x` at the site:

$$`\frac{x \text{ is a parameter of } f}{\mathrm{defines}_f(x, \mathsf{param})}`

$$`\frac{\begin{array}{c} b \in \mathrm{blocks}(f) \quad \mathrm{label}(b) = l \\ x \text{ is an argument of } b \end{array}}{\mathrm{defines}_f(x, \mathsf{arg}~l)}`

$$`\frac{\begin{array}{c} b \in \mathrm{blocks}(f) \quad \mathrm{label}(b) = l \\ x \text{ is a result of the op} \\ \text{at index } j \text{ of } b \end{array}}{\mathrm{defines}_f(x, \mathsf{result}~l~j)}`

Here $`\mathrm{label}(b)` is the label of the block $`b`. Only the
top-level blocks count: a value defined in a nested region has no
site here, so it is never in scope at a top-level op.
:::

:::readable Fir.Func.DominatesUse (fingerprint := "17419357972219174636")
*Definition: a definition dominates a use.* Let the op at index $`i` of the
block labelled $`l` use a value. A definition of it at the site $`s`
dominates that use, written $`s \mathrel{\mathrm{dom}_f} (l, i)`, when:

* the site is $`\mathsf{param}`: always, since a parameter is defined
  before the first op runs;
* the site is $`\mathsf{arg}~a`: $`a \mathrel{\mathrm{dom}_f} l`, so a block
  argument dominates the uses in its own block too;
* the site is $`\mathsf{result}~a~j`: either $`a = l` and $`j < i`, an
  earlier op of the same block, or $`a \neq l` and
  $`a \mathrel{\mathrm{dom}_f} l`.

An op never uses its own results, since $`j < i` is strict. The values that
a terminator passes to its successors are uses by the terminator, in its
own block, not by the target block.
:::

:::readable Fir.Func.InScope (fingerprint := "5383023758496433706")
*Definition: a use is in scope.* The use of $`x` by the op at index $`i` of
the block labelled $`l` is _in scope_ in $`f` when $`f` defines $`x` at
some site, and every site where $`f` defines $`x` dominates the use.

$$`\begin{aligned} & \mathrm{inscope}_f(x, l, i) \\ \iff\ & \exists\, s.\ \mathrm{defines}_f(x, s) \\ \wedge\ & \forall s.\ \mathrm{defines}_f(x, s) \\ & \quad \implies s \mathrel{\mathrm{dom}_f} (l, i) \end{aligned}`

The first half is _isolation from above_ (ADR-2026-10-29-2011): a function
uses only the values that it defines itself, never one defined outside
it. The second half is SSA dominance: on every path that
reaches the use, the value has been defined.
:::
