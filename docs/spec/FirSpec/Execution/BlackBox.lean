import VersoManual
import Fir.Execution.BlackBox
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on calls as black boxes, which renders
`Fir.Execution.BlackBox` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Calls as black boxes: readable blocks" =>

:::moduleDocs (fingerprint := "10351767067061231664")
:::

:::readable Fir.HVector.cast Fir.HVector.toDVals_cast Fir.HVector.forall₂_cast (fingerprint := "1918683470415412202")
*Definition and theorems: a vector seen at equal types.* Proof plumbing.
A vector of values of the types $`t^*` can be seen as a vector of the
types $`t'^*` when $`t^* = t'^*`. Seen so, it gives the same list of typed
values, and two vectors related position by position stay related. The
proofs below need it where a call's operand types are only known to equal
a callee's parameter types.
:::

:::readable Fir.SomeUB Fir.Allowed (fingerprint := "8502356157828630083")
*Definitions: UB at some budget, and a source that allows a path of the
target.* The proofs of the
next sections compare a run of ops in a source module with a run in a
target module. The source is taken at every budget: $`S_N` is its run with
$`N` steps of fuel. Then $`S` _hits UB at some budget_ when
$`\mathsf{ub}~r \in S_N` for some budget $`N` and reason $`r`, and $`S`
_allows_ an end $`e'` of the target as follows:

* a return $`\mathsf{ret}~(u'^*, k')` when $`S` hits UB at some budget, or
  $`\mathsf{ret}~(u^*, k) \in S_N` for some budget $`N`, some steps $`k`
  and values with $`u^* \sqsubseteq u'^*`;
* $`\mathsf{ub}~r'` when $`S` hits UB at some budget;
* $`\mathsf{fuel\_exhausted}`, and a stuck end, always: they ask nothing
  here.

This is the
{ref "The-fir-specification--Execution--Refinement"}[refinement of outcomes],
read for one path: UB of the source allows anything, and a return of the
target must return values that refine one of the source's. The budget of
the source is free, because the source may take more or fewer steps than
the target. Running out of fuel is handled apart, in the section on
{ref "The-fir-specification--Execution--Running-out-of-fuel___-followed-back"}[running out of fuel].
:::

:::readable Fir.BlackBox (fingerprint := "16627730904316910852")
*Definition: a black box.* Let $`M` be a source module and $`M'` a target
module, $`g` a function run in $`M` and $`g'` one run in $`M'`, and
$`\beta` a budget. The pair $`(g, g')` is a _black box_ with the bound $`\beta` when:

* _same parameters_: the parameter types of $`g'` are those of $`g`;
* _refines_: on all argument vectors $`a` and $`a'` of those types with
  $`a_i \sqsubseteq a'_i` for each $`i`, the
  {ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[observable behaviour]
  of the runs of $`g'` in $`M'` on $`a'` refines that of $`g` in $`M` on
  $`a`;
* _bounded_: on each argument vector $`a'`, either $`g'` in $`M'` runs out
  of fuel at every budget, or it runs out of fuel at no budget
  $`m \geq \beta`.

A call of $`g` in the source that the target runs as a call of $`g'` is
compared through these facts about the whole runs, without looking inside
them. That is what lets a callee's body change: the new body may take a
thousand steps where the old one took one, or the other way round. The
bound is what the section on
{ref "The-fir-specification--Execution--Running-out-of-fuel___-followed-back"}[running out of fuel]
needs to relate the two budgets.
:::

:::readable Fir.CallsRefined (fingerprint := "8421904290561493711")
*Definition: the target runs each call as the source does.* For modules
$`M` and $`M'` and a bound $`\beta`, every symbol $`s` names the same
function in both, $`\mathrm{lookup}_{M'}(s) = \mathrm{lookup}_M(s)`, or
$`M` has a function $`g = \mathrm{lookup}_M(s)` and $`M'` a function
$`g' = \mathrm{lookup}_{M'}(s)` such that $`(g, g')` is a black box with
the bound $`\beta`. Here $`\mathrm{lookup}_M(s)` is the function that a
call of $`s` runs in $`M`, as the
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter]
finds it.

A call of the same function is followed into its callee step by step; a
call of a black box is compared by the black box's facts. With no black
box, $`M'` is $`M`, which is the case of refined arguments.
:::

:::readable Fir.Ev.addLeft Fir.Func.call_cont (pin := Fir.Ahead) (fingerprint := "10367187128702594812")
*Definition and theorem: a caller goes on after its callee at the sum of
their budgets.*
For an end $`e` of a run of ops, $`e + k` is $`e` with $`k` more steps
left when it is a return, $`\mathsf{ret}~(u^*, i + k)` for
$`\mathsf{ret}~(u^*, i)`, and $`e` itself otherwise.

Let the call step of the
{ref "The-fir-specification--Execution--The-ways-a-step-goes-on"}[eighth way]
apply to the first op $`o` of $`o\,o'^*`: $`o` owns no region of the
core's kind, the values
$`v^*` of its operands are found in $`E`, $`o` is not a terminator and
calls the symbol $`s`, $`g = \mathrm{lookup}_M(s)`, and entering $`g`
with $`v^*` starts at the ops $`p^*` in the environment $`G`. Let
$`\mathsf{ret}~(u^*, k) \in \mathrm{run}_M(N_1, g, G, p^*)`, with the
types of $`u^*` the result types of $`o` and as many values as the names
$`x^*` of its results. Let $`e`, neither stuck nor
$`\mathsf{fuel\_exhausted}`, be an end of
$`\mathrm{run}_M(N_2, f, [x^* \mapsto u^*] \cdot E, o'^*)`. Then

$$`e + k \in \mathrm{run}_M(N_1 + N_2 + 1, f, E, o\,o'^*)`

Given $`N_2` more steps, the callee returns the same values and leaves
$`N_2` more, as the section on
{ref "The-fir-specification--Execution--The-runs-of-a-function___-and-fuel-monotonicity"}[the runs of a function]
proves; the rest then runs with $`k + N_2` steps, which is $`k` more than
it needed, and ends the same way, leaving $`k` more. A call adds the
budgets of its parts, which the refinement proofs use to put a source's
budget together from its callee's budget and that of the rest of the
caller's ops after the call.
:::

:::readable Fir.Func.run_inv Fir.Func.runs_ret_inv Fir.Func.runs_ub_inv Fir.Func.runs_exh_inv Fir.Func.runs_of_runOps (pin := Fir.Func.run) (pin := Fir.Func.runs) (pin := Fir.Ev.dropLeft) (fingerprint := "1560621121885559639")
*Theorems: the run of a function is the run of its entry block.* For a
function $`g` run in a module $`M`, an argument vector $`a` of its parameter
types and a budget $`N`, the
{ref "The-fir-specification--Execution--The-interpreter"}[run of the function]
enters $`g` with $`a`, then runs the ops it starts at, and drops the steps
that a return leaves. So:

* a path of the run of $`g` that is not stuck starts, at some ops $`p^*`
  in some environment $`G`, and is a path of $`\mathrm{run}_M(N, g, G, p^*)`
  with the steps left dropped;
* in particular, when the
  {ref "The-fir-specification--Execution--The-runs-of-a-function___-and-fuel-monotonicity"}[runs] of $`g`
  at $`N` on $`a` return $`u^*`, hit $`\mathsf{ub}~r`, or run out of
  fuel, $`g` starts, at $`p^*` in $`G`, and $`\mathrm{run}_M(N, g, G, p^*)`
  returns $`u^*` with some steps $`k` left, hits $`\mathsf{ub}~r`, or runs
  out of fuel;
* conversely, when $`g` starts at $`p^*` in $`G`, every end $`e` of
  $`\mathrm{run}_M(N, g, G, p^*)`, with the steps left dropped, is an end
  of the runs of $`g` at $`N` on $`a`.

This is the bridge between the black box's facts, which speak of whole
functions, and the proofs, which follow runs of ops.
:::

:::readable Fir.BlackBox.sig (pin := Fir.Func.enter) (fingerprint := "6148878215562349249")
*Theorem: a call that enters a black box's target passes arguments of the
source's parameter types.* Let $`(g, g')` be a black box. If entering
$`g'` with the typed values of a vector of the types $`t^*` starts, then
$`t^*` are the parameter types of $`g`. Entering checks the arguments'
types against the parameters', and the black box gives $`g'` the
parameter types of $`g`.
:::

:::readable Fir.BlackBox.allowed (pin := Fir.Allowed) (pin := Fir.SomeUB) (pin := Fir.BlackBox) (fingerprint := "2267193601829644512")
*Theorem: a black box's source allows what its target does.* Let
$`(g, g')` be a black box from $`M` to $`M'`, and let the vectors of
values $`a` and $`a'`, of the same types, satisfy $`a_i \sqsubseteq a'_i`
for each $`i`. Let entering $`g'` with $`a'` start at $`p'^*` in $`G'`,
and let $`e'`, neither stuck nor $`\mathsf{fuel\_exhausted}`, be an end of
$`\mathrm{run}_{M'}(n, g', G', p'^*)`. Then entering $`g` with $`a`
starts, at some $`p^*` in some $`G`, and the source
$`N \mapsto \mathrm{run}_M(N, g, G, p^*)` allows $`e'`: it hits UB at
some budget, or $`e'` returns values that refine values that the source
returns at some budget.

The target's path is a return or UB of the runs of $`g'`, so the
black box's refinement gives an outcome of $`g` that allows it: UB at some
budget, or a return of values that $`g'`'s refine. The theorem reads that
outcome back as a path of $`g`'s entry block. It is the step at which the
proof of the next section crosses a black-box call.
:::
