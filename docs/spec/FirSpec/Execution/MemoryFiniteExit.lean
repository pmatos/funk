import VersoManual
import Fir.Execution.MemoryFiniteExit
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a terminator's exits, with a budget, which renders
`Fir.Execution.MemoryFiniteExit` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "A terminator's exits, with a budget: readable blocks" =>

:::moduleDocs (fingerprint := "7737666910016553882")
:::

:::readable Fir.Func.memOps_notExhausted_exit (pin := Fir.OpsFinite) (fingerprint := "18348965580814033139")
*Theorem: a terminator's exits, with a budget.* Let the ops of the dialect
have finitely many outcomes, and let the terminator that starts
$`o~o^*` be monotone with memory. Let $`E \sqsubseteq E'` and
$`S \sqsubseteq S'`. If
$`\mathrm{ops}_M(\cdot, f, E, o~o^*) \mathbin{@} S` hits UB at no budget
and does not run out of fuel at $`N + 1`, and the run at $`N` of each block
the terminator may jump to has a budget at which the target's run does not
run out of fuel, then the target's run
$`\mathrm{ops}_{M'}(\cdot, f, E', o~o^*) \mathbin{@} S'` has one too. The
terminator goes on in finitely many ways in the target, each allowed by a
way it goes on in the source; the largest of their budgets, plus one,
serves. It is the terminator's case of
{ref "The-fir-specification--Memory--Divergence-with-ops-of-finitely-many-outcomes"}[divergence with ops of finitely many outcomes].
:::
