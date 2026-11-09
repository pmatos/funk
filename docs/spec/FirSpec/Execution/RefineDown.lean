import VersoManual
import Fir.Execution.RefineDown
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on running out of fuel, followed back,
which renders `Fir.Execution.RefineDown` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Running out of fuel, followed back: readable blocks" =>

:::moduleDocs (fingerprint := "12979570045138723279")
:::

:::readable Fir.AllowedBelow (pin := Fir.SomeUB) (fingerprint := "5689985325191484286")
*Definition: a source that allows a path at a budget, with a ratio of
steps.* Let $`B` be a number, $`S` a source, a run of ops at every budget
$`N`, written $`S_N`, and $`N` one budget. $`S` _allows at_ $`N`, _with
the ratio_ $`B`, an end $`e'` of the target as follows:

* $`\mathsf{fuel\_exhausted}` when $`\mathsf{fuel\_exhausted} \in S_N`, or
  $`S` hits UB at some budget;
* $`\mathsf{ret}~(u'^*, k')` when $`\mathsf{fuel\_exhausted} \in S_N`, or
  $`S` hits UB at some budget, or $`\mathsf{ret}~(u^*, k) \in S_N` for
  values with $`u^* \sqsubseteq u'^*` and steps with
  $`B \cdot (k + 1) \leq k'`;
* UB, and a stuck end, always: they ask nothing here.

A target that diverges runs out of fuel at every budget, and the source
must then diverge too, or hit UB at some budget. A path that runs out of
fuel holds no value to follow, so this relates budgets instead: the
target, with many more steps, either keeps the source running at $`N`, or
returns while leaving at least $`B` times the steps that the source
leaves, plus $`B`.
:::

:::readable Fir.AllowedBelow.of_someUB Fir.AllowedBelow.of_exhausted Fir.AllowedBelow.of_step Fir.AllowedBelow.of_not (pin := Fir.AllowedBelow) (pin := Fir.SomeUB) (fingerprint := "12827028900682239271")
*Theorems: four ways to show that a source allows a path at a budget.* Let
$`S` and $`C` be sources and $`B`, $`N` and $`N'` numbers.

* If $`S` hits UB at some budget, $`S` allows every end at every budget.
* If $`\mathsf{fuel\_exhausted} \in S_N`, $`S` allows every end at $`N`.
* If every end of $`C_N` that is not stuck is an end of $`S_{N'}`, and
  $`S` hits UB at some budget whenever $`C` does, then every end that
  $`C` allows at $`N`, $`S` allows at $`N'`, with the same ratio.
* $`S` allows every end that is UB or stuck, at every budget.

The third is how the proof below steps back from what the source does
after one op to the whole.
:::

:::readable Fir.BlackBox.allowedBelow (pin := Fir.AllowedBelow) (pin := Fir.BlackBox) (fingerprint := "1264385933521307406")
*Theorem: a black box's source allows its target's path at a budget.* Let
$`(g, g')` be a
{ref "The-fir-specification--Execution--Calls-as-black-boxes"}[black box]
from $`M` to $`M'` with the bound $`\beta`, and let the vectors of values
$`a` and $`a'`, of the same types, satisfy $`a_i \sqsubseteq a'_i` for
each $`i`. Let $`N_0` and $`n` be budgets with

$$`\beta + (\beta + 1) \cdot (N_0 + 1) \leq n`

Let entering $`g'` with $`a'` start at $`p'^*` in $`G'`, and let $`e'`,
neither stuck nor UB, be an end of $`\mathrm{run}_{M'}(n, g', G', p'^*)`.
Then entering $`g` with $`a` starts, at some $`p^*` in some $`G`, and the
source $`m \mapsto \mathrm{run}_M(m, g, G, p^*)` allows $`e'` at $`N_0`
with the ratio $`\beta + 1`.

Here the budgets part. If $`g'` diverges on $`a'`, the black box's
refinement gives that $`g` diverges on $`a`, so runs out of fuel at
$`N_0`, or hits UB at some budget. Otherwise $`g'` runs out of fuel at no
budget from $`\beta` on, so a run of it that returns uses at most
$`\beta` steps, and leaves at least $`n - \beta` of them. Then $`g` runs
out of fuel at $`N_0`, or, by
{ref "The-fir-specification--Execution--Fuel-and-progress"}[fuel monotonicity],
returns at $`N_0` what the black box allows, leaving at most $`N_0`
steps, which keeps the ratio.
:::

:::readable Fir.CallsRefined.callee_allowedBelow (pin := Fir.CallsRefined) (pin := Fir.AllowedBelow) (fingerprint := "8634306296257500461")
*Theorem: the source's callee allows what the target's callee does, at a
budget.* Let the target module $`M'` run each call as the source $`M`
does, with the bound $`\beta`, each symbol naming the same function in
both or a {ref "The-fir-specification--Execution--Calls-as-black-boxes"}[black box], and let every function of $`M` have
{ref "The-fir-specification--Execution--Returns-and-UB___-followed-back"}[monotone ops].
Let the symbol $`s` name the function $`g_0` in $`M'`, let
$`a \sqsubseteq a'`, position by position, be vectors of values of the
same types, and let entering $`g_0` with $`a'` start at $`p'^*` in $`G'`.
Let $`\beta + (\beta + 1) \cdot (N_0 + 1) \leq n`. Suppose that the
induction gives this, for these ops: if $`g_0` and $`p'^*` have monotone
ops, then for all {ref "The-fir-specification--Execution--Refined-environments"}[environments]
$`E \sqsubseteq E'`, every end of
$`\mathrm{run}_{M'}(n, g_0, E', p'^*)` is allowed at $`N_0` with the
ratio $`\beta + 1` by $`m \mapsto \mathrm{run}_M(m, g_0, E, p'^*)`. Then
for every end $`e'` of $`\mathrm{run}_{M'}(n, g_0, G', p'^*)` that is
neither stuck nor UB, $`s` names a function $`g` in $`M`, entering $`g`
with $`a` starts at some $`p^*` in some $`G`, and
$`m \mapsto \mathrm{run}_M(m, g, G, p^*)` allows $`e'` at $`N_0` with the
ratio $`\beta + 1`.

The same function is covered by the induction, and a black box by the
previous theorem.
:::

:::readable Fir.Func.runOps_allowedBelow (pin := Fir.AllowedBelow) (pin := Fir.CallsRefined) (pin := Fir.MonotoneOps) (pin := Fir.Func.OpsMonotone) (fingerprint := "18095261011233692718")
*Theorem: every path of the target that runs out of fuel or returns is
allowed by the source at a budget.* Let the target module $`M'` run each
call as the source $`M` does, with the bound $`\beta`: each symbol names
the same function in both, or a {ref "The-fir-specification--Execution--Calls-as-black-boxes"}[black box]. Let every function
of $`M` have
{ref "The-fir-specification--Execution--Returns-and-UB___-followed-back"}[monotone ops].
Then for every budget $`n`, every function $`f` with monotone ops, all
{ref "The-fir-specification--Execution--Refined-environments"}[environments] $`E \sqsubseteq E'`, every list of ops
$`o^*` with monotone ops, and every budget $`N` with

$$`(\beta + 1) \cdot (N + 1) \leq n`

every end $`e'` of the target's run $`\mathrm{run}_{M'}(n, f, E', o^*)`
is allowed at $`N`, with the ratio $`\beta + 1`, by the source
$`m \mapsto \mathrm{run}_M(m, f, E, o^*)`:

* if $`e' = \mathsf{fuel\_exhausted}`, the source runs out of fuel at
  $`N`, or hits UB at some budget;
* if $`e' = \mathsf{ret}~(u'^*, k')`, the source runs out of fuel at
  $`N`, or hits UB at some budget, or returns at $`N` values
  $`u^* \sqsubseteq u'^*`, leaving steps $`k` with
  $`(\beta + 1) \cdot (k + 1) \leq k'`;
* if $`e'` is UB or stuck, nothing is asked.

Calls and recursion are included. With the first case at every budget
$`N`, a target that diverges has a source that diverges or hits UB, which
is the half of refinement that the
{ref "The-fir-specification--Execution--Returns-and-UB___-followed-back"}[previous section]
leaves.

The proof is by strong induction on the target's budget. Each op takes
one step in both runs, a call of the same function included, whose callee
the induction covers, so the ratio holds with room to spare. A black-box
call is where the budgets part: a callee that returns in the target took
at most $`\beta` steps there, and with the call's own step, at most
$`\beta + 1` steps of the target stand for one or more of the source's.
So the target's path keeps $`\beta + 1` of its steps for each of the
source's, until the source runs out of fuel or hits UB, or to its end.
:::
