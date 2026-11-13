import VersoManual
import Fir.Core.CallFree
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on core functions without calls, which
renders `Fir.Core.CallFree` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Core functions without calls: readable blocks" =>

:::moduleDocs (fingerprint := "2122820304907451124")
:::

:::readable Fir.Core.Op.isCall Fir.Core.CallFree (fingerprint := "7508203294497242104")
*Definition: a call, and a function without calls.* A core op _is a
call_ when it is $`\mathsf{call}~g : t^* \to r^*`, for any symbol $`g`
and types $`t^*` and $`r^*`. A core function is _without calls_ when no
op of any of its blocks is a call. Whether a function is without calls
is decided by looking at each of its ops.
:::

:::readable Fir.Core.Op.total (pin := Fir.OpTotal) (fingerprint := "15209688528564269007")
*Theorem: every core op but $`\mathsf{call}` is total.* Every core op that
is not a call is
{ref "The-fir-specification--Execution--Poison-classes"}[total]: on every
operand vector, its semantics, or its exit for a terminator, has some
outcome. Each op's family proves it in its obligations, from
$`\mathsf{const}` to $`\mathsf{ret}`. $`\mathsf{call}` is left out: a run
never uses its semantics, and goes on by its callee's run
(ADR-2026-10-29-2006).
:::

:::readable Fir.Core.Op.exit_goto (pin := Fir.Core.Op.exit?) (pin := Fir.Core.brExit) (pin := Fir.Core.condBrExit) (pin := Fir.Core.Op.returnTypes) (pin := Fir.Core.retExit) (pin := Fir.Core.unreachableExit) (fingerprint := "4803048022170455550")
*Theorem: a core terminator that jumps goes to a successor that it has,
and gives no results.* For every core op $`o` that is a terminator, every
operand vector $`v^*` and every $`i`: if $`\mathrm{exit}_o(v^*)`, run in
the set monad, may end with $`\mathsf{goto}~i`, then
$`i < \mathrm{nsucc}(o)` and $`o` has no result types. Only
$`\mathsf{br}` and $`\mathsf{cond\_br}` jump, each to one of its
successors, and neither has results. $`\mathsf{ret}` returns, and
$`\mathsf{unreachable}` is UB.
:::

:::readable Fir.Core.Op.exit_ret (pin := Fir.Core.Op.exit?) (pin := Fir.Core.brExit) (pin := Fir.Core.condBrExit) (pin := Fir.Core.unreachableExit) (fingerprint := "1935509761369488939")
*Theorem: the only core op whose exit returns is $`\mathsf{ret}`.* For
every core op $`o` and operand vector $`v^*`: if $`\mathrm{exit}_o(v^*)`,
run in the set monad, may end with $`\mathsf{ret}`, then $`o` is
$`\mathsf{ret}~t^*` for some types $`t^*`. $`\mathsf{br}` always jumps,
$`\mathsf{cond\_br}` jumps, or hits UB on a poison condition, and
$`\mathsf{unreachable}` always hits UB.
:::

:::readable Fir.Core.Op.callee_none (pin := Fir.Core.Op.callTarget?) (fingerprint := "8972171092564716841")
*Theorem: a core op other than $`\mathsf{call}` calls no function.* For
every core op $`o` that is not a call, $`\mathrm{callee}(o)` is none: in
the core dialect, only $`\mathsf{call}` calls a function.
:::

:::readable Fir.Core.local_of_valid (pin := Fir.Func.Local) (pin := Fir.Core.Op.Valid) (pin := Fir.Core.Op.sig) (fingerprint := "11638370738824065083")
*Theorem: every valid core function without calls runs within itself.*
Let $`f` be a core function that is
{ref "The-fir-specification--Validation--The-general-rules"}[valid] in a
module context and without calls. Then $`f`
{ref "The-fir-specification--Execution--Progress-with-jumps-and-loops"}[runs within itself]:

* none of its ops calls a function, by the previous theorem;
* $`\mathsf{br}` and $`\mathsf{cond\_br}` go only to successors they have,
  and give no results;
* $`\mathsf{ret}~t^*`, the only op whose exit returns, takes operands of
  the types $`t^*`, which the
  {ref "The-fir-specification--Validation--Core-rules"}[core rule] of
  $`\mathsf{ret}` asks to be the result types of $`f`.
:::

:::readable Fir.Core.total_of_callFree (fingerprint := "9488280576929762062")
*Theorem: every op of a core function without calls is total.* If the
core function $`f` is without calls, every op of every block of $`f` is
total, since none of them is a call.
:::

:::readable Fir.Core.callFree_runsWell Fir.Core.callFree_fuelMonotone Fir.Core.callFree_progress Fir.Core.callFree_neverStuck (pin := Fir.Core.funcRuns) (pin := Fir.Core.RunsWell) (fingerprint := "799352563421054385")
*Theorem: a valid core function without calls runs well on every argument
vector, jumps and loops included.* Let $`M` be a core module and $`f` a
core function without calls, and let $`v^*` be a vector of values of the
parameter types of $`f`, poison included.

* If $`f` is valid in the
  {ref "The-fir-specification--Validation--The-general-rules"}[context]
  $`\mathrm{ctx}(M)` of $`M`, the runs
  $`\mathrm{runs}_M(f)(v^*)` run well: they are fuel-monotone, have
  progress and have no stuck path.
* If $`M` is
  {ref "The-fir-specification--Validation--The-general-rules"}[valid] and
  $`f` is one of its functions, the runs $`\mathrm{runs}_M(f)(v^*)` are
  fuel-monotone; they have progress; and they have no stuck path. These
  are the three obligations, one theorem each.

Here $`\mathrm{runs}_M(f)(v^*)` is the
{ref "The-fir-specification--Execution--The-runs-of-core-functions"}[runs of f]
on $`v^*`, at each budget, and to
{ref "The-fir-specification--Execution--The-runs-of-core-functions"}[run well]
is to meet the three
{ref "The-fir-specification--Execution--Fuel-and-progress"}[obligations].
The first needs only the validity of $`f` itself: $`f` calls no
function, so the other functions of $`M` play no part, and $`f` need not
even be one of them. They follow from the theorems on functions that run
within themselves. Branches and loops are included; a function with a
$`\mathsf{call}` op runs other functions of its module, and the
{ref "The-fir-specification--Execution--Core-functions-with-calls"}[next section]
covers it.
:::
