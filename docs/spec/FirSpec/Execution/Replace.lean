import VersoManual
import Fir.Execution.Replace
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on replacing a callee, which renders
`Fir.Execution.Replace` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Replacing a callee: readable blocks" =>

:::moduleDocs (fingerprint := "2953035155584653121")
:::

:::readable Fir.Func.runs_exhausted_down (fingerprint := "8224768621522136213")
*Theorem: a function that runs out of fuel runs out of fuel with fewer
steps.* For every function $`f`, run in a module $`M`, argument vector $`a`
and budgets $`n \leq m`: if the
{ref "The-fir-specification--Execution--The-runs-of-a-function___-and-fuel-monotonicity"}[runs]
of $`f` on $`a` run out of fuel at $`m`, they run out of fuel at $`n`.
It is the theorem of the section on
{ref "The-fir-specification--Execution--The-ways-a-step-goes-on"}[the ways a step goes on]
for a whole function. So on each argument vector, a function runs out of
fuel at every budget, or from some budget on never does.
:::

:::readable Fir.exists_common_bound (fingerprint := "4821431095657372811")
*Theorem: one bound serves finitely many argument vectors.* Let the list
$`L` hold every element of a set $`A`, and let $`Q(a, m)` be a property of
an element $`a \in A` and a number $`m` that passes to smaller numbers:
$`m \leq m'` and $`Q(a, m')` give $`Q(a, m)`. Then there is a $`\beta` such
that for every $`a \in A`, either $`Q(a, m)` holds for every $`m`, or it
holds for no $`m \geq \beta`.

With $`Q(a, m)` "the new callee runs out of fuel at $`m` on $`a`", this
gives the black box its bound when the callee's parameter types have
finitely many argument vectors (`docs/decisions/semantics-refinement.md#congruence-in-the-callee`). Without that, one
bound may not serve them all: a caller whose arguments grow without limit
can make the new callee run longer and longer before it returns.
:::

:::readable Fir.Func.runs_replaceBody_isRefinedBy (pin := Fir.FuncRuns.IsRefinedBy) (pin := Fir.Func.OpsMonotone) (pin := Fir.BlackBox) (fingerprint := "17377090128024739525")
*Theorem: congruence in the callee.* In every dialect, let $`M` be a
module, and suppose that:

* every function of $`M` has
  {ref "The-fir-specification--Execution--Returns-and-UB___-followed-back"}[monotone ops];
* the refinement of values is reflexive, $`v \sqsubseteq_t v`, and
  transitive, $`u \sqsubseteq_t v` and $`v \sqsubseteq_t w` giving
  $`u \sqsubseteq_t w`, for every type $`t`;
* no two functions of $`M` have the same symbol;
* $`g` is a function of $`M` with the symbol $`s`, $`b` a region, and the
  parameter types of $`g` have finitely many argument vectors;
* with $`M' = M[s \leftarrow b]` and $`g' = g[s \leftarrow b]`, the runs
  of $`g'` in $`M'`
  {ref "The-fir-specification--Execution--Refinement"}[refine]
  the runs of $`g` in $`M`: on every argument vector $`a`, the observable
  behaviour of $`g'` in $`M'` refines that of $`g` in $`M`.

Then for every function $`f` of $`M`, the runs of $`f[s \leftarrow b]` in
$`M'` refine the runs of $`f` in $`M`: $`f` itself, or $`g'` when $`f`
is $`g`. Calls and recursion are included (`docs/decisions/semantics-refinement.md#congruence-in-the-callee`).

This is what makes a compiler's pass over one function sound for the
whole program: replace a callee by a body that, run in the new module,
refines it, and every caller is refined.

The hypothesis compares $`g'` in the new module with $`g` in the old. A
callee that calls back, itself or its callers, calls the new body in
$`M'`, so only its runs in $`M'` say what a call of it does there. A
weaker hypothesis, that $`g'` run in the old module refines $`g`, would
make the theorem false: if $`g` returns $`0`, the body that calls $`s`
and returns its result refines it in $`M`, where it calls the old body;
in $`M'` it calls itself, and never returns.

The proof makes every call of $`s` a
{ref "The-fir-specification--Execution--Calls-as-black-boxes"}[black box]
from $`g` in $`M` to $`g'` in $`M'`, and every other symbol names the
same function in both. The black box refines: on refined arguments,
$`g` is refined by itself, by
{ref "The-fir-specification--Execution--Refined-arguments"}[refined arguments],
and that by $`g'`, by the hypothesis, and refinement is transitive. Its
bound is the one bound for the finitely many argument vectors, above. The
section on refined arguments then gives the theorem for each $`f` other
than $`g`. Monotonicity is asked only of the old module's functions: a
call of $`s` is a black box, whose new body the proof does not run.
:::
