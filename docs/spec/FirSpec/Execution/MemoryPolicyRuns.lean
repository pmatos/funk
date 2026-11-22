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

:::moduleDocs (fingerprint := "17971604853313405782")
:::

:::readable Fir.Func.memBehaviour (pin := Fir.RunItems.withAddrs) (pin := Fir.observable) (fingerprint := "7040573654846431868")
*Definition: the behaviour under every policy.* The observable behaviour
with memory of the function $`f` of $`M` on the arguments $`\vec{a}`,
with the items $`L`, is

$$`\mathrm{beh}(f, \vec{a}) = \bigcup_{g} \mathrm{obs}(\mathrm{runs}_{L[\mathrm{addrs} := g]}(f, \vec{a}))`

the outcomes of its runs with memory under some address policy $`g` for
each memory, chosen once for every budget of fuel, with the resolvers of
$`L`. The spec's behaviour also lets the run choose its resolvers, below.
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

:::readable Fir.Func.memRunsUnder Fir.Func.Kept (pin := Fir.RunItems.withResolvers) (fingerprint := "6322419569217851262")
*Definitions: the resolvers kept.* The runs of $`f` on $`\vec{a}` under
the policies $`g` and the resolvers $`k` are those with the items
$`L[\mathrm{addrs} := g, \mathrm{resolvers} := k]`. The resolvers $`k` are
kept under $`g` when those runs never end in UB, or when the runs under
$`g` end in UB under every resolver: the choice is angelic, so the spec
keeps the resolvers that avoid UB when one does (the human's ruling of
2026-11-20 on #232, question A).
:::

:::readable Fir.Func.angelicBehaviour (fingerprint := "12081253149103447825")
*Definition: the spec's behaviour.* The observable behaviour with memory
of $`f` on $`\vec{a}`, with the items $`L`, is

$$`\mathrm{beh}^{\ast}(f, \vec{a}) = \bigcup_{g} \bigcup_{k \text{ kept under } g} \mathrm{obs}(\mathrm{runs}_{L[\mathrm{addrs} := g, \mathrm{resolvers} := k]}(f, \vec{a}))`

a union over the policies, which the implementation chooses, and over the
resolvers kept under each, which the run chooses to keep the program
defined. A union over every resolver would make the program UB when one
resolver ends in UB, which is not angelic.
:::

:::readable Fir.Func.angelicBehaviour_of_observable Fir.Func.angelicBehaviour_of_noUB (fingerprint := "9178524160503808562")
*Theorems: a run under one policy and resolver.* Each outcome of a run
under the policies and resolvers of its items is one of the spec's when
that resolver is kept, and so when those runs never end in UB, on any
path at any budget of fuel. So the outcomes of `fir-ref`, under the
canonical policy and resolver, are the spec's when its runs never end in
UB; when they do, another resolver may avoid the UB.
:::

:::readable Fir.Func.angelicBehaviour_isRefinedBy Fir.Func.angelicBehaviour_isRefinedBy_of_each (fingerprint := "12581916420485410482")
*Theorems: refinement of the spec's behaviour.* The spec's behaviour of
$`f` is refined by that of $`f'` when each resolver kept for $`f'` under a
policy is matched by one kept for $`f` under it, whose runs those of $`f'`
refine. So a refinement that holds under each policy and resolver holds
of the spec's behaviour when $`f'` ends in UB under each policy and
resolver under which $`f` does. Without that, $`f'` could avoid UB under a
resolver that $`f` drops for it, and keep its outcomes there.
:::
