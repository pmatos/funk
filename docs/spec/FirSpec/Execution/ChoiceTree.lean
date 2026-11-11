import VersoManual
import Fir.Execution.ChoiceTree
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on choice trees, which renders
`Fir.Execution.ChoiceTree` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Choice trees: readable blocks" =>

:::moduleDocs (fingerprint := "1147497501033574720")
:::

:::readable Fir.ChoiceTree (fingerprint := "6945210103657211533")
*Definition: a tree of choices.* A tree of choices is a computation written
out as a tree, so that a program can walk it. A path from the root to a
leaf is one way the run may go. Its results are in a set $`A`, and $`E` is the set of reasons for which a path
may end with no outcome.

```grammar Fir.ChoiceTree
\mathit{tree}
pure        \mathsf{pure}~a \quad (a \in A)
ub          \mathsf{ub}~\mathit{reason}
noOutcome   \mathsf{no\_outcome}~e \quad (e \in E)
choose      \mathsf{choose}~w~(b \mapsto \mathit{tree}_b)
```

* $`\mathsf{pure}~a`: the path ends with the result $`a`.
* $`\mathsf{ub}~\mathit{reason}`: the path ends with
  {ref "The-fir-specification--Execution--Poison-and-immediate-UB"}[immediate UB].
* $`\mathsf{no\_outcome}~e` (`noOutcome` in the Lean): the path ends with
  no outcome at all, for the reason $`e`. An op without execution rules
  ends its path so, since the set monad gives it the empty set of ways to
  end (ADR-2026-10-30-1855).
* $`\mathsf{choose}~w~(b \mapsto \mathit{tree}_b)`: the path chooses $`w`
  bits, and goes on with the subtree $`\mathit{tree}_b` for the bits
  $`b`. The node has one subtree for each of the $`2^w` vectors of $`w`
  bits.
:::

:::readable Fir.ChoiceTree.bind (pin := Fir.ChoiceTree.instMonad) (pin := Fir.ChoiceTree.instMonadChoice) (pin := Fir.ChoiceTree.instMonadUB) (fingerprint := "6710891819122759510")
*Definition: the steps of a computation, as trees.* To run a tree $`t`,
then $`g` on its result, $`t \mathbin{>\!\!>\!\!=} g` puts $`g(a)` in place
of each leaf $`\mathsf{pure}~a` of $`t`, and keeps its other leaves and
its choices:

$$`\begin{aligned} \mathsf{pure}~a \mathbin{>\!\!>\!\!=} g & = g(a) \\ \mathsf{ub}~r \mathbin{>\!\!>\!\!=} g & = \mathsf{ub}~r \\ \mathsf{no\_outcome}~e \mathbin{>\!\!>\!\!=} g & = \mathsf{no\_outcome}~e \end{aligned}`

$$`\begin{aligned} & \mathsf{choose}~w~(b \mapsto t_b) \mathbin{>\!\!>\!\!=} g \\ & \quad = \mathsf{choose}~w~(b \mapsto t_b \mathbin{>\!\!>\!\!=} g) \end{aligned}`

With it, trees are a monad: a value $`a` is the leaf $`\mathsf{pure}~a`,
the {ref "The-fir-specification--Execution--Effects-and-op-semantics"}[choice]
of $`w` bits is the node
$`\mathsf{choose}~w~(b \mapsto \mathsf{pure}~b)`, and
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[UB]
with a reason $`r` is the leaf $`\mathsf{ub}~r`. So the
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter],
written once for any monad with these effects, also runs in trees.
:::

:::readable Fir.ChoiceTree.toSet (fingerprint := "3155849494660982669")
*Definition: the set of a tree.* The set $`\mathrm{set}(t)` of a tree $`t`
holds the ways its paths end, as a computation of the
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[set monad]:

$$`\begin{aligned} \mathrm{set}(\mathsf{pure}~a) & = \{ \mathsf{ok}~a \} \\ \mathrm{set}(\mathsf{ub}~r) & = \{ \mathsf{ub}~r \} \\ \mathrm{set}(\mathsf{no\_outcome}~e) & = \emptyset \end{aligned}`

$$`\mathrm{set}(\mathsf{choose}~w~(b \mapsto t_b)) = \textstyle\bigcup_b \mathrm{set}(t_b)`

A path with no outcome adds nothing, and a choice gathers the ways of all
its subtrees. This set is the meaning of a tree, and what the theorems
about `fir-ref`'s modes compare their walks against.
:::

:::readable Fir.ChoiceTree.toSet_bind Fir.ChoiceTree.toSetMorphism (pin := Fir.SetM.instMonad) (fingerprint := "7195744646405943446")
*Theorem: the set of a sequence is the sequence of the sets.* For every
tree $`t` and every $`g` from results to trees,

$$`\mathrm{set}(t \mathbin{>\!\!>\!\!=} g) = \mathrm{set}(t) \mathbin{>\!\!>\!\!=} (a \mapsto \mathrm{set}(g(a)))`

where the sequence on the right is the set monad's: every way $`g(a)`
may end for each result $`a` of $`t`, and every UB of $`t`.

*Definition: the set of a tree is a monad morphism.* So $`\mathrm{set}`
keeps the steps of a computation: a value, a sequence, and applying a
function to a result. It is a
{ref "The-fir-specification--Execution--Monad-morphisms"}[monad morphism]
from trees to the set monad. By the previous section, a run of the
interpreter in trees then has, as its set, the run in the set monad, once
each op's semantics in trees has the op's semantics in the set monad as
its set.
:::

:::readable Fir.ChoiceTree.toSet_choose Fir.ChoiceTree.toSet_ub (pin := Fir.SetM.instMonadChoice) (pin := Fir.SetM.instMonadUB) (fingerprint := "6036697414325508384")
*Theorem: the effects are the same in both monads.* For every width
$`w`, the set of the choice of $`w` bits is the set monad's choice of
$`w` bits, every vector of $`w` bits; and for every reason $`r`, the set
of UB with $`r` is the set monad's UB with $`r`, $`\{\mathsf{ub}~r\}`.
Op rules that are written once for any monad with these effects, such as
those of the core dialect, therefore have the same meaning in trees as in
the set monad.
:::

:::readable Fir.ChoiceTree.toSet_mapsFrame (pin := Fir.ChoiceTree.instMonadFrame) (fingerprint := "16826740269587007722")
*Theorem: the set of a tree keeps frames.* A tree has no memory, so a
frame of a tree is the tree itself, as a frame of the set monad is the
computation itself; $`\mathrm{set}` therefore keeps frames, and the
{ref "The-fir-specification--Execution--Monad-morphisms"}[interpreter's morphism theorem]
applies to it.
:::
