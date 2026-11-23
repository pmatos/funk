import VersoManual
import Fir.Execution.CallsAt
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the callee of a call, which renders
`Fir.Execution.CallsAt` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The callee of a call: readable blocks" =>

:::moduleDocs (fingerprint := "15435611383271580653")
:::

:::readable Fir.callee_budget (fingerprint := "5452247528708767008")
*Lemma: the callee's budget.* For numbers $`\beta`, $`N_0`, $`n` and
$`n'` with $`n' \le n \le n' + 1`, $`n - n' \le N_0` and
$`\beta + (\beta + 1)(N_0 + 1) \le n`:

$$`\beta + (\beta + 1)(N_0 - (n - n') + 1) \le n'`

A call that leaves its callee all the steps its op leaves, or all but
one, leaves the callee a budget large enough for the source's callee at
$`N_0 - (n - n')`, when the op leaves enough for the source at $`N_0`.
The refinement proofs that follow a run down a budget use it at each call.
:::

:::readable Fir.Func.CallsAt Fir.Func.CallsAt.le Fir.Func.CallsAt.up Fir.Func.CallsAt.down Fir.Func.CallsAt.at Fir.Func.CallsAt.picked_of_lt (pin := Fir.Module.callable) (fingerprint := "6293265155228083810")
*Definition: the call of an op.* The op $`o` of the module $`M`, on the
operands $`v^*`, with $`n` steps left after its own, _calls_ the symbol
$`s` on the arguments $`a^*` with $`n'` steps left for the call, in one of
two ways:

$$`\frac{\mathrm{callee}(o) = \mathsf{fixed}~s}{\mathrm{calls}_M(o, v^*, n) = (s, v^*, n)}
\qquad
\frac{\mathrm{callee}(o) = \mathsf{picked} \quad s \in \mathrm{pick}_o(\mathrm{callable}_M(t^*, \mathrm{ret}(o)), v^*)}{\mathrm{calls}_M(o, v^*, n + 1) = (s, \mathrm{tail}(v^*), n)}`

where $`t^*` is the operand types of $`o` but the first, and
$`\mathrm{tail}(v^*)` is $`v^*` without its first value. An op that names
its callee calls it on its operands with the steps it leaves; an op whose
callee is picked calls the symbol its rule picks, on its operands but the
first, after one more step, the call's (#235).

*Theorems.* A call leaves its callee $`n'` steps with
$`n' \le n \le n' + 1`. With $`j` more steps after the op, the same call
leaves its callee $`j` more. With $`j` fewer steps, it leaves its callee
$`j` fewer, unless the callee is picked and the op leaves no step for the
call. A call calls the same symbol, on the same arguments, at every budget
that leaves the call $`m` steps, $`m + (n - n')`. A call that leaves its
callee fewer steps than its op leaves picks its callee.
:::

:::readable Fir.Func.CallsAt.source (pin := Fir.PickMonotone) (fingerprint := "11679764903621011898")
*Theorem: a call of the target is a call of the source.* Let the operands
$`v^*` refine $`v'^*` position by position, let the module $`M'` call
each symbol that $`M` can call, at the same types, and let the rule of
$`o` be monotone when its callee is picked. If $`o` in $`M'`, on
$`v'^*`, calls $`s` on $`a'^*` with $`n'` steps, then either $`o` in
$`M`, on $`v^*`, calls the same $`s` with the same steps on arguments
$`a^*` that $`a'^*` refines position by position, or the callee of $`o`
is picked and its rule, on $`v^*` in $`M`, may end with UB, which allows
anything. The refinement proofs follow a call of the target back to the
source by it.
:::
