import VersoManual
import Fir.Execution.MemoryBlackBox
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on calls as black boxes, with memory,
which renders `Fir.Execution.MemoryBlackBox` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "Calls as black boxes, with memory: readable blocks" =>

:::moduleDocs (fingerprint := "7122691847001462072")
:::

:::readable Fir.MemAllowed Fir.MemAllowed.of_someUB Fir.MemAllowed.of_not Fir.MemAllowed.of_step (pin := Fir.SomeUB) (pin := Fir.Ev.addLeft) (fingerprint := "16450805183566433580")
*Definition and theorems: a path allowed by a source.* A source, a run
$`\mathit{src}_N` at each budget $`N` whose returns carry what refines,
_allows_ a path of the target when it hits UB at some budget, or, for a
return of $`a'`, it returns at some budget some $`a \sqsubseteq a'`. A path
that runs out of fuel or is stuck asks nothing here. As for runs in the set
monad
({ref "The-fir-specification--Execution--Returns-and-UB___-followed-back"}[returns and UB, followed back]):
UB at some budget allows every path; and a path that the rest of a run
allows is allowed by the whole, when each way the rest ends at $`N` is a
way the whole ends at $`N_0 + N + 1`, with $`k` more steps left on a
return.
:::

:::readable Fir.Func.memCall_allowed (pin := Fir.Func.memCall) (fingerprint := "7030202911306346812")
*Theorem: leaving a frame keeps what is allowed.* When each path of the
target callee's ops, from $`\mathrm{enter}(S')`, is allowed by the source's
from $`\mathrm{enter}(S)`, each path of the target callee in its frame from
$`S'` is allowed by the source's in its frame from $`S`: a return of
$`(\vec{w}, T)` allowed by $`(\vec{w}_0, T_0)` with
$`T_0 \sqsubseteq T` leaves the frame with
$`\mathrm{exit}(T_0) \sqsubseteq \mathrm{exit}(T)`.
:::

:::readable Fir.Func.memCall_cont (pin := Fir.Ev.addLeft) (fingerprint := "17481982894339671064")
*Theorem: a caller's budget is its callee's plus its rest's.* A caller
whose callee, in its frame, returns $`((\vec{w}, T), k)` at the budget
$`N_1`, and whose rest of ops from $`T` ends at the budget $`N_2`, ends so
at $`N_1 + N_2 + 1`, leaving $`k` more steps: with more fuel, the callee
returns the same, with the same memories, and leaves more steps.
:::

:::readable Fir.FuncRuns.BoundedBy Fir.MemBlackBox Fir.MemCallsRefined (pin := Fir.Func.memRunsFrom) (fingerprint := "11146693213621817567")
*Definitions: bounded runs, black boxes with memory, and modules whose
calls refine.* Runs $`f` are _bounded_ by the budget $`B` when, on each
input, they diverge, or none of them with $`B` steps or more runs out of
fuel. A _black box with memory_ is a function $`g` of the source module $`M` and a
function $`g'` of the target module $`M'` with the same parameter types,
such that:

* on arguments $`\vec{v} \sqsubseteq \vec{v}'` and from memories
  $`S \sqsubseteq S'`, the observable behaviour of $`g'` in $`M'` from
  $`S'` refines that of $`g` in $`M` from $`S`, the memories they end with
  included
  ({ref "The-fir-specification--Memory--Runs-from-given-memories"}[runs from given memories]);
* the runs of $`g'` from given memories are bounded by $`\mathit{bound}`.

The target module _runs each call with memory as the source does_ when each
symbol names the same function in both, or a black box with memory. A
callee runs from the memories its caller reached, so a black box speaks of
runs from every memories, not only from the empty ones.
:::

:::readable Fir.MemBlackBox.sig Fir.MemBlackBox.allowed (fingerprint := "4319915142181417683")
*Theorems: a black-box call, allowed.* A call that enters a black box's
target passes arguments of the parameter types of its source. A return or
UB of the target in its frame, called on arguments and from memories that
refine the source's, is allowed by the source's callee in its frame, which
starts: the black box's refinement gives a return of the source with values
and memories that the target's refine, or UB at some budget.
:::
