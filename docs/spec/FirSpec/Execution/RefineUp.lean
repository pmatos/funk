import VersoManual
import Fir.Execution.RefineUp
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on returns and UB, followed back, which
renders `Fir.Execution.RefineUp` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Returns and UB, followed back: readable blocks" =>

:::moduleDocs (fingerprint := "16275544034918685054")
:::

:::readable Fir.MonotoneOps Fir.Func.OpsMonotone (pin := Fir.OpMonotone) (fingerprint := "11196719689786516999")
*Definition: ops whose own rules are monotone.* A list of ops $`o^*` has
_monotone ops_ when every op of it that runs by its own rule, a terminator
or an op with no callee, is
{ref "The-fir-specification--Execution--Poison-classes"}[monotone]: on
operands that refine others position by position, every way its semantics
may end, or every place its exit may go, is allowed by a way it may end,
or the same place, on those others. A function _has monotone ops_ when
the ops of each of its blocks do.

A call is left out: it has no rule of its own, and what it does is its
callee's run, which the proofs follow instead (ADR-2026-11-02-1514). The
proofs ask this only of the ops that a run can reach, not of every op
instance of the dialect (ADR-2026-11-05-1715), so a dialect whose ops are
monotone only at valid op instances still meets it for every function of
a valid module.
:::

:::readable Fir.Func.OpsMonotone.enter Fir.Func.OpsMonotone.jump (fingerprint := "12032502672585873761")
*Theorems: a run stays among the ops of its function.* Let the function
$`f` have monotone ops. When entering $`f` starts at the ops $`p^*`, they
have monotone ops; and when a jump of $`f` goes to the block $`b`, the
ops of $`b` have monotone ops. Both are the ops of a block of $`f`, the
entry block or the block that a label names. This keeps the invariant of
the proof below along a run, through jumps and loops.
:::

:::readable Fir.Allowed.of_someUB Fir.Allowed.of_not Fir.Allowed.of_step (pin := Fir.Allowed) (pin := Fir.SomeUB) (pin := Fir.Ev.addLeft) (fingerprint := "6725602533761279265")
*Theorems: three ways to show that a source allows a path.* Let $`S` and
$`C` be sources, each a run of ops at every budget.

* If $`S` hits UB at some budget, $`S` allows every end.
* $`S` allows every end that is stuck or $`\mathsf{fuel\_exhausted}`.
* Let $`N_0` and $`k` be numbers. If, for every budget $`N`, every end
  $`x` of $`C_N` that is neither stuck nor $`\mathsf{fuel\_exhausted}`
  gives $`x + k \in S_{N_0 + N + 1}`, then every end that $`C` allows,
  $`S` allows. Here $`x + k` is $`x` with $`k` more steps left when it
  is a return, and $`x` otherwise.

Here a source _allows_ an end of the target as the section on
{ref "The-fir-specification--Execution--Calls-as-black-boxes"}[black boxes]
defines: a return when the source hits UB at some budget or returns, at
some budget, values that the target's refine; UB when the source hits UB
at some budget; anything else always. The third is how the proof below
steps back: $`C` is what the source does after one op, and $`S` the whole,
one step longer, or longer by a callee's budget too, which leaves $`k`
more steps.
:::

:::readable Fir.CallsRefined.callee_allowed (pin := Fir.CallsRefined) (fingerprint := "17587604883499326604")
*Theorem: the source's callee allows what the target's callee does.* Let
the target module $`M'` run each call as the source $`M` does, with the
bound $`\beta`: each symbol names the same function in both, or a
{ref "The-fir-specification--Execution--Calls-as-black-boxes"}[black box]. Let every function of $`M` have monotone ops. Let the
symbol $`s`
name the function $`g_0` in $`M'`, let $`a \sqsubseteq a'`, position by
position, be vectors of values of the same types, and let entering $`g_0`
with $`a'` start at the ops $`p'^*` in the environment $`G'`. Suppose that
the induction gives this, for these ops: if $`g_0` and $`p'^*` have
monotone ops, then for all
{ref "The-fir-specification--Execution--Refined-environments"}[environments]
$`E \sqsubseteq E'`, every end of
$`\mathrm{run}_{M'}(n, g_0, E', p'^*)` is allowed by the source
$`N \mapsto \mathrm{run}_M(N, g_0, E, p'^*)`. Then for every end $`e'` of
$`\mathrm{run}_{M'}(n, g_0, G', p'^*)` that is neither stuck nor
$`\mathsf{fuel\_exhausted}`, $`s` names a function $`g` in $`M`, entering
$`g` with $`a` starts at some $`p^*` in some $`G`, and the source
$`N \mapsto \mathrm{run}_M(N, g, G, p^*)` allows $`e'`.

When $`s` names the same function in both modules, it is a function of
$`M`, so its ops are monotone, and it starts at the same ops on $`a` as on
$`a'`, in an environment refined by the target's, which the induction
covers. When $`s` names a black box, the
{ref "The-fir-specification--Execution--Calls-as-black-boxes"}[black box's source allows]
what its target does.
:::

:::readable Fir.Func.runOps_allowed (pin := Fir.Allowed) (pin := Fir.CallsRefined) (pin := Fir.MonotoneOps) (pin := Fir.Func.OpsMonotone) (fingerprint := "9919193492215224188")
*Theorem: every return and every UB of the target is allowed by the
source.* Let the target module $`M'` run each call as the source $`M`
does, with some bound $`\beta`: each symbol names the same function in
both, or a {ref "The-fir-specification--Execution--Calls-as-black-boxes"}[black box]. Let every function of $`M` have monotone
ops. Then for every budget $`n`, every function $`f` with monotone ops,
all {ref "The-fir-specification--Execution--Refined-environments"}[environments]
$`E \sqsubseteq E'` and every list of ops $`o^*` with monotone ops,
every end $`e'` of the target's run $`\mathrm{run}_{M'}(n, f, E', o^*)`
is {ref "The-fir-specification--Execution--Calls-as-black-boxes"}[allowed] by the source
$`N \mapsto \mathrm{run}_M(N, f, E, o^*)`:

* if $`e' = \mathsf{ret}~(u'^*, k')`, the source hits UB at some budget,
  or returns at some budget values $`u^*` with $`u^* \sqsubseteq u'^*`;
* if $`e' = \mathsf{ub}~r'`, the source hits UB at some budget;
* if $`e'` is $`\mathsf{fuel\_exhausted}` or stuck, nothing is asked.

Calls and recursion are included. This is half of refinement through
calls: the returns and UB of the target. Divergence is the
{ref "The-fir-specification--Execution--Running-out-of-fuel___-followed-back"}[other half].

The proof is by strong induction on the target's budget, for every
function at once, and follows the target's path by the
{ref "The-fir-specification--Execution--The-ways-a-step-goes-on"}[eight ways]
a step goes on:

* The op's operands are found in the source's environment too,
  {ref "The-fir-specification--Execution--Refined-environments"}[refined].
  The op is monotone, so what it does on the target's operands is allowed
  by what it does on the source's: UB there allows anything; otherwise
  the source gives results that the target's refine, or jumps to the same
  block. The environments after the op stay refined, and the induction
  covers the rest, with one step less.
* A call is allowed by the source's callee, by the previous theorem, with
  the induction for a callee that is the same function.
* When the source's callee returns at the budget $`N_1` values that the
  target's refine, and the source's rest is allowed at the budget
  $`N_2`, the source's run at $`N_1 + N_2 + 1` is allowed:
  {ref "The-fir-specification--Execution--Calls-as-black-boxes"}[a caller goes on after its callee]
  at the sum of their budgets.
:::
