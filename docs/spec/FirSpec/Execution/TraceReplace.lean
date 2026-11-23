import VersoManual
import Fir.Execution.TraceReplace
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on congruence in the callee over traced
runs, returns and UB, which renders `Fir.Execution.TraceReplace`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Congruence in the callee over traced runs: returns and UB: readable blocks" =>

:::moduleDocs (fingerprint := "5131638045090122057")
:::

:::readable Fir.Func.traceRunsFrom_tAllowed Fir.Func.traceRunsFrom_ret_allowed Fir.Func.traceRunsFrom_ub_allowed (fingerprint := "5561435148282997304")
*Theorems: returns and UB from a traced state, call by call.* For a dialect
whose ops show events, let the target module $`M'` run each call in the
traced layer as the source $`M` does, and every terminator and every op
with no callee of $`f` and of $`M`'s functions be monotone in the traced
layer,
the external-call rule at each of their calls included. On arguments
$`\vec{v} \sqsubseteq \vec{v}'` and from traced states
$`s \sqsubseteq s'`, each path of $`f`'s entry block's ops in its frame in
$`M'` is allowed at some budget by $`f`'s in $`M`. So each
$`\mathsf{ret}~t'~(\vec{w}', s_1')` of the traced runs of $`f` in $`M'`
from $`s'` is allowed by UB after a refined prefix of $`t'`, or by some
$`\mathsf{ret}~t~(\vec{w}, s_1)` in $`M` from $`s` with
$`t \sqsubseteq t'`, $`\vec{w} \sqsubseteq \vec{w}'` and
$`s_1 \sqsubseteq s_1'`; and each $`\mathsf{ub}~t'~r'` by UB after a
refined prefix of $`t'`.
:::

:::readable Fir.Func.traceRuns_ret_iff_from Fir.Func.traceRuns_ub_iff_from (fingerprint := "10279653960785745419")
*Theorems: from the memories a run starts with.* A return of a function's
traced runs, seen at its end, is a return of its traced runs from the
memories that hold $`L`'s starting allocations, with nothing escaped, its values and the memories and escaped allocations of
the traced state it ends in; UB is UB after the same marked trace.
:::

:::readable Fir.Func.traceRuns_calls_ret_allowed Fir.Func.traceRuns_calls_ub_allowed (fingerprint := "2079837471260775434")
*Theorems: returns and UB of the traced runs.* Under the same hypotheses,
on arguments $`\vec{v} \sqsubseteq \vec{v}'`, a poison by any value, each
$`\mathsf{ret}~t'~o'` of the traced runs of $`f` in $`M'` is allowed by
UB after a refined prefix of $`t'`, or by some $`\mathsf{ret}~t~o` in $`M`
with $`t \sqsubseteq t'` and $`o \sqsubseteq o'`, when refinement of values
is transitive: memories that refine others, with the same allocations
escaped, give ends that refine each other. Each $`\mathsf{ub}~t'~r'` is
allowed by UB after a refined prefix of $`t'`.
:::

:::readable Fir.Module.replaceBody_traceCallsRefined (fingerprint := "6844210484100796195")
*Theorem: replacing a callee's body gives calls refined.* Let the symbols
of $`M` be unique, every terminator and every op with no callee of its
functions be monotone in the traced layer,
the external-call rule at each of their calls included, every op and every
external call have finitely many outcomes given the world's answers, and
refinement of values and of events
be transitive. Replace the body of its function $`g` by $`b`, so that
$`g`, run in the new module $`M'` from given traced states, refines $`g`
in $`M`. Then $`M'` runs each call in the traced layer as $`M` does: $`g`
is a traced black box, since $`g` on $`(\vec{v}, s)` is refined by $`g`
on $`(\vec{v}', s')` (refined arguments from a traced state), which is
refined by the new $`g`, by the hypothesis; every other symbol names the
same function in both.
:::
