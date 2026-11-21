import VersoManual
import Fir.Execution.TraceArgs
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on refined arguments over traced runs: returns, UB and each budget, which renders
`Fir.Execution.TraceArgs` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Refined arguments over traced runs: returns, UB and each budget: readable blocks" =>

:::moduleDocs (fingerprint := "3788918816789127072")
:::

:::readable Fir.Result.Finished Fir.Result.finishEnd Fir.TraceEnd.Allows.finishEnd (fingerprint := "3788084618345794415")
*Definition: finished runs.* A run of a function finishes a run of its
entry block's ops: a return gives back its values, without the steps
left. What a source's run of a function ends with allows what the
target's ends with when both return, the second's values refining the
first's, or both run out of fuel.

*Theorem.* Finishing keeps one way of ending allowing another in step.
:::

:::readable Fir.Func.traceRun_iff Fir.Func.traceRun_allowed (fingerprint := "8379465532877309952")
*Theorem: the traced run of a function.* A path of the traced run of $`f`
on $`\vec{v}` that is not stuck finishes a path of its entry block's ops,
run in its frame.

*Theorem: refined arguments, in step.* When every terminator and every op
with no callee of $`f` and of the module's functions is monotone in the
traced layer, then on arguments $`\vec{v} \sqsubseteq \vec{v}'`, from
traced states $`s \sqsubseteq s'`, at every budget $`n`, each path of the
run of $`f` on $`\vec{v}'` from $`s'` that is not stuck is allowed by a
path of its run on $`\vec{v}` from $`s` at the same budget.
:::

:::readable Fir.List.IsRefinedPrefix.getElem? Fir.Func.traceRuns_path_allowed (fingerprint := "1113848085572077889")
*Theorem: a refined prefix, place by place.* A refined prefix of $`l'` is
refined, at each of its places, by the element of $`l'` there.

*Theorem: the traced runs of a dialect with events.* For a dialect whose
ops are monotone by its rules in the traced layer, at $`\ell`, $`\rho` and
$`L`, each path of a function's traced runs on $`\vec{v}'` that is not
stuck comes from a path of its run in the traced layer of marked traces
that a path of its run on $`\vec{v}`, at the same budget, allows, from the
memories that hold $`L`'s starting allocations, with nothing escaped.
:::

:::readable Fir.Func.traceRuns_exhausted_allowed Fir.Func.traceRuns_ub_allowed Fir.Func.traceRuns_ret_allowed (fingerprint := "14754067560585736861")
*Theorems: returns, UB and each budget.* For a dialect whose ops show
events, when every terminator and every op with no callee of $`f` and of
the module's functions is monotone in the traced layer, on arguments
$`\vec{v} \sqsubseteq \vec{v}'`, a poison by any value:

* at each budget, each path of the traced runs on $`\vec{v}'` that runs
  out of fuel with the marked trace $`m'` is allowed by a path on
  $`\vec{v}` that runs out of fuel with $`m \sqsubseteq m'`, or hits UB
  with a refined prefix of $`m'`;
* each $`\mathsf{ub}~t'~r'` of the traced observable behaviour on
  $`\vec{v}'` is allowed by some $`\mathsf{ub}~t~r` on $`\vec{v}`, $`t` a
  refined prefix of $`t'`;
* when refinement of values is transitive, each $`\mathsf{ret}~t'~o'` on
  $`\vec{v}'` is allowed by UB after a refined prefix of $`t'`, or by
  $`\mathsf{ret}~t~o` with $`t \sqsubseteq t'` and $`o \sqsubseteq o'`:
  memories that refine others, with the same allocations escaped, give
  ends that refine each other.

Divergence, silent or with acts forever, needs one trace of the source at
every budget, and the next stage gives it.
:::
