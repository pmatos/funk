import VersoManual
import Fir.Execution.MemoryRefineDown
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on running out of fuel with memory,
followed back, which renders `Fir.Execution.MemoryRefineDown`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Running out of fuel with memory, followed back: readable blocks" =>

:::moduleDocs (fingerprint := "17266900686647129922")
:::

:::readable Fir.MemAllowedBelow Fir.MemAllowedBelow.of_someUB Fir.MemAllowedBelow.of_exhausted Fir.MemAllowedBelow.of_not Fir.MemAllowedBelow.of_step (pin := Fir.SomeUB) (fingerprint := "13951263104922388177")
*Definition and theorems: a path allowed below a budget.* The source at
the budget $`N` allows, below the ratio $`B`, a path of the target that
runs out of fuel or returns $`(a', k')`, when it runs out of fuel at $`N`,
or hits UB at some budget, or, on a return, returns at $`N` some
$`(a, k)` with $`a \sqsubseteq a'` and $`B(k + 1) \le k'`. A path that hits
UB or is stuck asks nothing here. As for runs in the set monad
({ref "The-fir-specification--Execution--Running-out-of-fuel___-followed-back"}[running out of fuel, followed back]),
UB at some budget and running out of fuel at $`N` allow every path, and
what the rest of a run allows, the whole allows.
:::

:::readable Fir.Func.memCall_allowedBelow (pin := Fir.Func.memCall) (fingerprint := "7075980611033959191")
*Theorem: leaving a frame keeps what is allowed below a budget.* When each
path of the target callee's ops from $`\mathrm{enter}(S')` that runs out of
fuel or returns is allowed at $`N_0` by the source's from
$`\mathrm{enter}(S)`, so is each such path of the target callee in its
frame from $`S'` by the source's in its frame from $`S`: leaving a frame
keeps refinement of memories.
:::

:::readable Fir.MemBlackBox.allowedBelow Fir.MemCallsRefined.callee_allowedBelow (pin := Fir.MemBlackBox) (pin := Fir.MemCallsRefined) (fingerprint := "12850138011807003321")
*Theorems: a callee's path that runs out of fuel or returns, allowed below a
budget.* A path of a black box's target in its frame that runs out of fuel
or returns, called on arguments and from memories that refine the
source's, at a budget of at least
$`\mathit{bound} + (\mathit{bound} + 1)(N_0 + 1)`, is allowed below the
ratio $`\mathit{bound} + 1` by the source's callee in its frame at
$`N_0`. If the target diverges there, the source diverges or hits UB; if
not, the target returns within $`\mathit{bound}` steps, and the source,
whose runs from given memories are fuel-monotone, runs out of fuel at
$`N_0` or returns there what the black box allows. A callee that is the same
function in both modules is covered by the induction.
:::
