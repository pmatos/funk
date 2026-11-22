import VersoManual
import Fir.Execution.TraceRefine
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on refinement over the traced runs of a dialect with no event, which renders
`Fir.Execution.TraceRefine` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Refinement over the traced runs of a dialect with no event: readable blocks" =>

:::moduleDocs (fingerprint := "11935382029869136311")
:::

:::readable Fir.Func.traceRuns_args_isRefinedBy_of_lawful (fingerprint := "3666097375113157725")
*Theorem: refined arguments over traced runs.* For a dialect lawful in its
monotonicity whose ops show no event, when the refinement of values is
transitive, in a module whose functions are all valid, wherever a run names
the dialect's memories:

$$`\vec{v} \sqsubseteq \vec{v}' \implies \mathrm{traced}(f, \vec{v}) \sqsubseteq \mathrm{traced}(f, \vec{v}')`

calls and recursion included, from refined arguments with memory, from the
memories a run starts with.
:::

:::readable Fir.Func.traceRuns_replaceBody_isRefinedBy_of_bound Fir.Func.traceRuns_replaceBody_isRefinedBy_of_opsFinite (fingerprint := "8233574276402944445")
*Theorems: congruence in the callee over traced runs.* For a dialect lawful
in its monotonicity whose ops show no event, when the refinement of values
is reflexive and transitive, in a valid module $`M`: if $`@g` with the new
body $`b`, run in $`M[g := b]` from given memories, refines $`@g` in $`M`,
then every function $`f` of $`M` is refined over its traced runs by $`f`
with $`@g`'s new body in $`M[g := b]`. One form asks for a budget past
which the new $`@g` runs out of fuel only if it diverges; the other asks
for none when every op that runs by its own rule has finitely many
outcomes. Both follow from congruence with memory, from the memories a
run starts with.
:::
