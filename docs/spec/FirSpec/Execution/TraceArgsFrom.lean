import VersoManual
import Fir.Execution.TraceArgsFrom
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on refined arguments over traced runs
from a given traced state, which renders `Fir.Execution.TraceArgsFrom`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Refined arguments over traced runs from a given traced state: readable blocks" =>

:::moduleDocs (fingerprint := "7079564547442309146")
:::

:::readable Fir.Func.traceRunsFrom Fir.Func.traceRunsFrom_truncates Fir.Func.traceRunsFrom_finitelyMany (fingerprint := "14861942271792698399")
*Definition: a function's traced runs from a traced state.* At $`\ell`,
$`\rho` and $`L`, the traced runs of $`f` in $`M` from given traced states
run $`f` on each argument vector from each traced state, each op that runs
by the dialect's rule showing a step before it, and return its values with
the traced state each return ends in.

*Theorems.* They truncate, with any $`W > 0` that exceeds the length of
every chain of calls of the module by at least two. When every op that
runs by its own rule, every external call and every rule that picks a
callee
has finitely many outcomes given the world's answers, they
have finitely many traces at each budget.
:::

:::readable Fir.Func.traceRunsFrom_path_allowed Fir.Func.traceRunsFrom_isRefinedBy_of_args (fingerprint := "10676232841159578254")
*Theorem: refined arguments from a traced state.* For a dialect whose ops
show events, let every terminator and every op with no callee of $`f` and of
the module's functions be monotone in the traced layer,
the external-call rule at each of their calls included. At every budget,
each path of the traced runs of $`f` on $`\vec{v}'` from $`s'` that is not
stuck is allowed in step by a path on $`\vec{v}` from $`s`, when
$`\vec{v} \sqsubseteq \vec{v}'` and $`s \sqsubseteq s'`. When every op also
has finitely many outcomes given the world's answers,

$$`\mathrm{traceObservable}(f_M(\vec{v}, s)) \sqsubseteq \mathrm{traceObservable}(f_M(\vec{v}', s'))`

the traced state each return ends in included: returns, UB, silent
divergence and acts forever.
:::
