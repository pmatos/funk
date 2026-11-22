import VersoManual
import Fir.Execution.TraceChain
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on calls between two steps, which renders
`Fir.Execution.TraceChain` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Calls between two steps: readable blocks" =>

:::moduleDocs (fingerprint := "1571611182379316198")
:::

:::readable Fir.Module.callHead? Fir.Module.CallChain Fir.Module.CallChain.unique (fingerprint := "11229309543807958068")
*Definition: chains of calls.* $`\mathrm{callHead}_M(os)` is the ops of
the entry block of the function of $`M` that the first op of $`os` calls,
when that op is a call of a function of $`M` with an entry block. The ops
$`os` start a chain of $`c` calls when $`c` such calls follow each other
into entry blocks, before an op that is not one:

$$`\frac{\mathrm{callHead}_M(os) = \mathsf{none}}{\mathrm{chain}_M(os, 0)}
\qquad
\frac{\mathrm{callHead}_M(os) = \mathsf{some}~body \quad \mathrm{chain}_M(body, c)}{\mathrm{chain}_M(os, c + 1)}`

*Theorem.* A list of ops starts at most one chain.
:::

:::readable Fir.Module.callHead?_terminator Fir.Module.callHead?_noCallee Fir.Module.callHead?_call (fingerprint := "5494783123581111281")
*Theorems.* A terminator and an op with no callee start no call. A call of
a function of the module that enters it starts a call of its entry block's
ops.
:::

:::readable Fir.Module.callHead?_noFunc (fingerprint := "11358993282750030086")
*Theorem.* Ops whose first op calls a symbol that names no function of
the module, as a call to an external declaration does, start no call: the
call runs by the external-call rule, and enters no callee.
:::

:::readable Fir.Module.exists_callBound (fingerprint := "9455717655566123013")
*Theorem: the bound.* Every module $`M` has a $`W > 0` with $`c + 1 \le W`
whenever $`\mathrm{chain}_M(os, c)`: a chain that starts with a call goes
on from the entry block of one of the finitely many functions of $`M`.
:::

:::readable Fir.Func.traceOps_silent (fingerprint := "1301248812232124812")
*Theorem: a cycle never shows a step again.* When $`os` starts no chain,
only an endless one, every path of a traced run of $`os` that is not stuck
runs out of fuel and shows nothing: each call calls again in its callee,
and never returns.
:::
