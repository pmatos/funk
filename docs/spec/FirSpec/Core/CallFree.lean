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

:::moduleDocs (fingerprint := "16927633626146534009")
:::

:::readable Fir.Core.Op.isCall Fir.Core.CallFree (fingerprint := "7508203294497242104")
*Definition: a call, and a function without calls.* A core op _is a
call_ when it is $`\mathsf{call}~g : t^* \to r^*`, for any symbol $`g`
and types $`t^*` and $`r^*`. A core function is _without calls_ when no
op of any of its blocks is a call. Whether a function is without calls
is decided by looking at each of its ops.
:::

:::readable Fir.Core.Op.total (pin := Fir.OpTotal) (fingerprint := "10277650597748481361")
*Theorem: every core op but $`\mathsf{call}` and $`\mathsf{alloca}` is
total in the set monad.* Every core op that is not a call and touches no
memory is
{ref "The-fir-specification--Execution--Poison-classes"}[total]: on every
operand vector, its semantics, or its exit for a terminator, has some
outcome. Each op's family proves it in its obligations, from
$`\mathsf{const}` to $`\mathsf{ret}`. $`\mathsf{call}` is left out: a run
never uses its semantics, and goes on by its callee's run
(ADR-2026-10-29-2006). $`\mathsf{alloca}` is left out too: it has no rule
in the set monad, and is total with memory by
{ref "The-fir-specification--Memory--Stack-allocation-obligations"}[its own rule].
:::

:::readable Fir.Core.Op.exit_goto (pin := Fir.Core.Op.exit?) (pin := Fir.Core.brExit) (pin := Fir.Core.condBrExit) (pin := Fir.Core.Op.returnTypes) (pin := Fir.Core.retExit) (pin := Fir.Core.unreachableExit) (fingerprint := "6103530266710620474")
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

:::readable Fir.Core.local_of_valid (pin := Fir.Func.Local) (pin := Fir.Core.Op.Valid) (pin := Fir.Core.Op.sig) (fingerprint := "45745022842253262")
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
