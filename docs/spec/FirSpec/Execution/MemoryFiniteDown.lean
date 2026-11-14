import VersoManual
import Fir.Execution.MemoryFiniteDown
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on divergence with ops of finitely many
outcomes, which renders `Fir.Execution.MemoryFiniteDown`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Divergence with ops of finitely many outcomes: readable blocks" =>

:::moduleDocs (fingerprint := "8732878515543511956")
:::

:::readable Fir.Func.memOps_notExhausted_of_finite (pin := Fir.OpsFinite) (pin := Fir.MemCallsRefined) (pin := Fir.SomeUB) (pin := Fir.MemMonotoneOps) (pin := Fir.Func.MemOpsMonotone) (fingerprint := "9542362405041666030")
*Theorem: a source that does not run out of fuel bounds its target.* Let
the target module $`M'` run each call with memory as the source $`M` does,
the ops of the dialect have finitely many outcomes, and every op of
$`M`'s functions, of $`f` and of $`o^*` that runs by its own rule be
monotone with memory. Let $`E \sqsubseteq E'` and $`S \sqsubseteq S'`. If
$`\mathrm{ops}_M(\cdot, f, E, o^*) \mathbin{@} S` hits UB at no budget and
does not run out of fuel at $`N`, then at some budget $`n`,
$`\mathrm{ops}_{M'}(n, f, E', o^*) \mathbin{@} S'` does not run out of fuel
either:

$$`\neg\,\mathrm{UB}(\mathrm{ops}_M) \wedge \mathrm{exh} \notin \mathrm{ops}_M(N) \implies \exists n.\ \mathrm{exh} \notin \mathrm{ops}_{M'}(n)`

The proof is by strong induction on $`N`. An op that runs by its own rule
goes on in finitely many ways in the target, each allowed by a way it goes
on in the source, whose rest at $`N - 1` does not run out of fuel; the
largest of their budgets, plus one, serves. A call's callee has a budget at
which it does not run out of fuel: by the induction for the same function,
and for a black box because its target cannot diverge where its source does
not. At that budget the callee returns finitely many things, each allowed
by a return of the source's callee at $`N - 1`, after which the rest of the
source does not run out of fuel; the callee's budget plus the largest of
the rests', plus one, serves. No black box needs a budget of its own for
every input.
:::
