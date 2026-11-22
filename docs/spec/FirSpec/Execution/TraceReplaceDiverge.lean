import VersoManual
import Fir.Execution.TraceReplaceDiverge
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on congruence in the callee over traced runs, divergence included, which renders
`Fir.Execution.TraceReplaceDiverge` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Congruence in the callee over traced runs, divergence included: readable blocks" =>

:::moduleDocs (fingerprint := "17610753270981007049")
:::

:::readable Fir.Stream.IsRefinedBy.closed (fingerprint := "5280672388205635261")
*Theorem.* A stream refined by a closed stream is closed.
:::

:::readable Fir.Func.traceRunsFrom_isRefinedBy_of_calls (fingerprint := "3291851347794863516")
*Theorem: refinement when calls are refined.* For a dialect whose ops show
events, let $`M'` run each call in the traced layer as $`M` does, every
terminator and every op with no callee of $`f` and of $`M`'s functions be
monotone in the traced layer,
the external-call rule at each of their calls included, and every op and every
external call have finitely many outcomes given
the world's answers. On arguments $`\vec{v} \sqsubseteq \vec{v}'`, a poison by
any value, and from traced states $`s \sqsubseteq s'`, the traced runs of
$`f` in $`M'` from $`(\vec{v}', s')` refine those of $`f` in $`M` from
$`(\vec{v}, s)`, the traced state each return ends in included. A return or
UB is allowed call by call; a divergence, silent or with acts forever, by
divergence across black boxes.
:::

:::readable Fir.Func.traceRuns_diverge_iff_from Fir.Func.traceRuns_reacts_iff_from Fir.Func.traceRuns_isRefinedBy_of_traceRunsFrom (fingerprint := "5252632761560559523")
*Theorems: from the memories a run starts with.* A function's traced runs
diverge silently after $`t`, or show the infinite trace $`T`, exactly when
its traced runs from the memories that hold $`L`'s starting allocations do:
the same paths run out of fuel. So, when refinement of values is
transitive, traced runs from those memories with nothing escaped that
refine others give traced runs, each return seen at its end,
that refine theirs.
:::

:::readable Fir.Func.traceRunsFrom_replaceBody_isRefinedBy Fir.Func.traceRuns_replaceBody_isRefinedBy (fingerprint := "3136690538283535608")
*Theorems: congruence in the callee, divergence included.* For a dialect
whose ops show events, let the symbols of $`M` be unique, every terminator
and every op with no callee of its functions be monotone in the traced
layer,
the external-call rule at each of their calls included, every op and every
external call have finitely many outcomes given the world's answers, and
refinement of values be reflexive and transitive and refinement of events
transitive. Replace the
body of its function $`g` by $`b`, so that $`g`, run in the new module $`M'`
from given traced states, refines $`g` in $`M`. Then every function $`f` of
$`M` is refined by its new version in $`M'`, over traced runs from given
traced states and over traced runs, each return seen at its end: $`M'` runs
each call as $`M` does, by replacing a callee's body, and refinement when
calls are refined applies. A divergence of the new module, silent or with
acts forever, is allowed by the old one even when the new callee takes a
different number of steps.
:::
