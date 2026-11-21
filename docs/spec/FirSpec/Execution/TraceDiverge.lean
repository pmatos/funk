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

:::moduleDocs (fingerprint := "10147136709900058212")
:::

:::readable Fir.Func.traceRuns_truncates Fir.Func.traceRuns_finitelyMany (fingerprint := "16935286989464333339")
*Theorems.* The traced runs of a function truncate, with any $`W > 0` that
exceeds the length of every chain of calls of the module by at least one.
When every op that runs by its own rule has finitely many outcomes, given
the world's answers, they have finitely many traces at each budget.
:::

:::readable Fir.Func.traceRuns_isRefinedBy_of_args (fingerprint := "16076026329311882144")
*Theorem: refined arguments over traced runs.* For a dialect whose ops
show events, let every terminator and every op with no callee of $`f` and
of the module's functions be monotone in the traced layer, every op have
finitely many outcomes given the world's answers (the human's ruling of
2026-11-20), and refinement of values be transitive. Then on arguments
$`\vec{v} \sqsubseteq \vec{v}'`, a poison by any value, at $`\ell`,
$`\rho`, $`L`, $`\mu` and any rule for addresses,

$$`\mathrm{traceObservable}(f(\vec{v})) \sqsubseteq \mathrm{traceObservable}(f(\vec{v}'))`

returns, UB, silent divergence and acts forever included.
:::
