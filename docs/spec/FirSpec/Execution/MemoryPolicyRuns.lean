import VersoManual
import Fir.Execution.MemoryPolicyRuns
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on runs under every address policy,
which renders `Fir.Execution.MemoryPolicyRuns` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "Runs under every address policy: readable blocks" =>

:::moduleDocs (fingerprint := "5911238001146547632")
:::

:::readable Fir.Func.memBehaviour (pin := Fir.RunItems.withAddrs) (pin := Fir.observable) (fingerprint := "14920681031559595295")
*Definition: the behaviour under every policy.* The observable behaviour
with memory of the function $`f` of $`M` on the arguments $`\vec{a}`,
with the items $`L`, is

$$`\mathrm{beh}(f, \vec{a}) = \bigcup_{g} \mathrm{obs}(\mathrm{runs}_{L[\mathrm{addrs} := g]}(f, \vec{a}))`

the outcomes of its runs with memory under some address policy $`g` for
each memory, chosen once for every budget of fuel.
:::

:::readable Fir.Func.memBehaviour_of_observable (fingerprint := "597765761385849776")
*Theorem: a run under one policy.* Each outcome of a run under one policy,
the canonical layout that `fir-ref` runs included, is an outcome of the
behaviour under every policy: the items under their own policies are the
items.
:::

:::readable Fir.Func.memBehaviour_isRefinedBy (fingerprint := "14339623532216338174")
*Theorem: refinement under each policy.* When the runs of $`f` on
$`\vec{a}` are refined by those of $`f'` on $`\vec{a}'` under each
policy, the behaviour of $`f` under every policy is refined by that of
$`f'`.
:::
