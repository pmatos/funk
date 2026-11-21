import VersoManual
import Fir.Execution.TraceDiverge
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on refined arguments over traced runs, divergence included, which renders
`Fir.Execution.TraceDiverge` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Refined arguments over traced runs, divergence included: readable blocks" =>

:::moduleDocs (fingerprint := "15255307916607136838")
:::

:::readable Fir.Func.traceRuns_exhausted_iff Fir.Func.traceRuns_exhausted_iff_from Fir.Func.traceRuns_truncates Fir.Func.traceRuns_finitelyMany (fingerprint := "8123228927819801441")
*Theorems.* A path of a function's traced runs that runs out of fuel is a
path of its entry block's ops, in a frame from the empty memories with
nothing escaped, that runs out of fuel after the same marked trace, and a
path of its traced runs from that traced state (those of the section on
refined arguments from a given traced state) that does so. The
traced runs of a function truncate, with any $`W > 0` that
exceeds the length of every chain of calls of the module by at least one.
When every op that runs by its own rule has finitely many outcomes, given
the world's answers, they have finitely many traces at each budget. Both hold because they hold
of the traced runs from a traced state.
:::

:::readable Fir.Func.traceRuns_isRefinedBy_of_args (fingerprint := "16076026329311882144")
*Theorem: refined arguments over traced runs.* For a dialect whose ops
show events, let every terminator and every op with no callee of $`f` and
of the module's functions be monotone in the traced layer, every op have
finitely many outcomes given the world's answers (the hypothesis the human
ruled on 2026-11-20, in its form by position), and refinement of values be transitive. Then on arguments
$`\vec{v} \sqsubseteq \vec{v}'`, a poison by any value, at $`\ell`,
$`\rho`, $`L`, $`\mu` and any rule for addresses,

$$`\mathrm{traceObservable}(f(\vec{v})) \sqsubseteq \mathrm{traceObservable}(f(\vec{v}'))`

returns, UB, silent divergence and acts forever included.
:::
