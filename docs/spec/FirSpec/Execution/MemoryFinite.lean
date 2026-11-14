import VersoManual
import Fir.Execution.MemoryFinite
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on ops of finitely many outcomes, which
renders `Fir.Execution.MemoryFinite` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Ops of finitely many outcomes: readable blocks" =>

:::moduleDocs (fingerprint := "3592964032077437555")
:::

:::readable Fir.SetM.FinitelyMany Fir.FinitelyMany Fir.FinitelyMany.lift (fingerprint := "18420379536908109690")
*Definitions and theorem: finitely many outcomes.* A computation $`x` of
the set monad has _finitely many results_ when some list holds every
$`a` with $`\mathrm{ok}(a) \in x`. A computation $`c` of the state layer
has _finitely many outcomes_ when, from each state $`S`, some list holds
every $`(a, S')` with $`\mathrm{ok}(a, S') \in c(S)`. UB is not counted. A
computation of the set monad with finitely many results, lifted into the
state layer, has finitely many outcomes: from $`S` it ends with $`S`.
:::

:::readable Fir.ChoiceTree.toSet_finitelyMany (pin := Fir.ChoiceTree.toSet) (fingerprint := "16613946475129314555")
*Theorem: a tree of choices has finitely many results.* The set of the ways
a tree's paths end has finitely many results: a leaf has at most one, and a
choice of $`w` bits has $`2^w` subtrees, each with finitely many.
:::

:::readable Fir.List.exists_cover Fir.List.exists_budget (fingerprint := "12144165027478046457")
*Theorems: finitely many lists, finitely many budgets.* When each member
$`a` of a list has a list that holds every $`b` with $`P(a, b)`, one list
holds every such $`b` of every member: their concatenation. When each
member $`a` has a budget $`m` with $`Q(a, m)`, and $`Q(a, \cdot)` holds of
every larger budget once it holds, one budget serves every member: the
largest.
:::

:::readable Fir.FinitelyManyRets Fir.FinitelyManyRets.mapVal (fingerprint := "1331002861433453914")
*Definition and theorem: a run that returns finitely many things.* A run
_returns finitely many things_ when some list holds every $`b` it may
return. Mapping its returns keeps that.
:::

:::readable Fir.OpsFinite (fingerprint := "5574973558946288833")
*Definition: ops of finitely many outcomes.* The ops of a dialect have
finitely many outcomes, in a semantics in the state layer over the
memories, when each op that runs by its own rule, a terminator or an op
with no callee, on each operands, has finitely many outcomes: its results
with the memories, as an op that is not a terminator, and where control
goes with the memories, as a terminator. It is how the assumption of
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[observable behaviour],
that every choice has finitely many options, reads with memory.
:::

:::readable Fir.Func.memCall_exhausted_iff Fir.Func.memCall_ub_of_memOps Fir.Func.memOps_notExhausted_up Fir.Func.memCall_notExhausted_up (pin := Fir.Func.memCall) (fingerprint := "5589302038012358630")
*Theorems: running out of fuel at a budget.* A callee in its frame from
$`S` runs out of fuel exactly when its ops do from $`\mathrm{enter}(S)`,
and UB of its ops is UB of the callee in its frame. A run of ops, or of a
callee in its frame, that does not run out of fuel at a budget $`m` does
not at any budget $`m' \ge m`: a path that runs out of fuel at $`m'` runs
out of fuel at $`m`.
:::

:::readable Fir.Func.memOps_finitelyManyRets Fir.Func.memCall_finitelyManyRets (pin := Fir.Func.memOps) (fingerprint := "13117006857750135887")
*Theorems: a run at one budget returns finitely many things.* When the ops
of the dialect have finitely many outcomes, the run of ops
$`\mathrm{ops}_M(n, f, E, o^*) \mathbin{@} S` returns finitely many things,
for every function, environment, ops and memories, and so does a callee in
its frame. The proof is by strong induction on $`n`, following
{ref "The-fir-specification--Memory--The-ways-a-step-with-memory-goes-on"}[the ways a step goes on]:
an op that runs by its own rule goes on in finitely many ways, each into a
rest with fewer steps; a callee returns finitely many things at $`n`, each
followed by a rest with at most $`n` steps.
:::
