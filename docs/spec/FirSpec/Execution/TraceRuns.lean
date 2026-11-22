import VersoManual
import Fir.Execution.TraceRuns
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on traced runs, which renders
`Fir.Execution.TraceRuns` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Traced runs: readable blocks" =>

:::moduleDocs (fingerprint := "11627704792050292624")
:::

:::readable Fir.Step Fir.Step.acts Fir.Step.actsOf Fir.Step.upTo (fingerprint := "8705614873626702449")
*Definition: a marked trace.* A marked trace is a list of steps
$`\mathsf{tick}` and acts. Its acts, $`\mathrm{acts}(m)`, are its trace,
the steps removed. What it shows in its first $`N` steps,
$`m|_N`, is its elements before its step $`N + 1`.
:::

:::readable Fir.Step.actsOf_upTo_prefix Fir.Step.actsOf_upTo_eq_nil (fingerprint := "15683290872420861338")
*Theorem: the first steps show a prefix.* The acts of $`m|_N` are a prefix
of the acts of $`m`. So a marked trace with no act shows none in its first
steps.
:::

:::readable Fir.TRun Fir.traceObservable (fingerprint := "14692163008125237661")
*Definition: a traced run.* A traced run at one budget is the set of the
ways it may end, each with its marked trace: a result or a stuck path, or UB
with its reason.

*Definition: traced observable behaviour.* For a run $`R_n` at each budget
$`n`, its traced observable behaviour holds:

* $`\mathsf{ret}~t~o` and $`\mathsf{ub}~t~r` when some budget reaches them
  with a marked trace whose acts are $`t`;
* $`\mathsf{diverge}~t` when there is a number $`N` of steps such that, at
  every budget $`n`, the run can run out of fuel with a marked trace $`m`
  whose acts are a prefix of $`t`, and $`\mathrm{acts}(m|_N) = t` when
  $`N \le n`;
* $`\mathsf{reacts}~T` when there are numbers $`K(k)` of steps such that, at
  every budget $`n`, the run can run out of fuel with a marked trace $`m`
  whose acts are a prefix of $`T`, and $`m|_{K(k)}` has at least $`k` acts
  whenever $`K(k) \le n`.

The steps date the acts. Without them, a run that can return arbitrarily
late after its last act would also fall silent after it, and a run that can
show arbitrarily many acts before it returns would also show acts forever.
When every choice, the answers to an event among them, has finitely many
options, the paths that meet one of these conditions at every budget are,
by König's lemma, the prefixes of one infinite path that shows $`t` and then
falls silent, or shows $`T`.
:::

:::readable Fir.TRun.NoActs Fir.traceObservable_of_noActs (fingerprint := "2589735741253907909")
*Definition: a run that shows no act.* A traced run $`R` shows no act and
ends as the run $`s` of the set monad when none of its marked traces holds
an act, it has a path that ends with the result $`x` exactly when $`s` has
$`\mathsf{ok}~x`, and one that ends in UB for the reason $`r` exactly when
$`s` has $`\mathsf{ub}~r`.

*Theorem: with no act, the traced behaviour is the behaviour.* The traced
observable behaviour of runs that show no act is the
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[observable behaviour]
of the runs they end as, each outcome with an empty trace. Divergence is
silent from the start, and the run shows no infinite trace.
:::

:::readable Fir.FuncTraceRuns Fir.FuncTraceRuns.IsRefinedBy (pin := Fir.FuncTraceRuns.instHRefinement) (fingerprint := "4035688308089087198")
*Definition: the traced runs of functions.* The traced runs of a function
are its traced run on each argument vector at each budget. A target
function refines a source function when, on every argument vector, its
traced observable behaviour refines the source's.
:::

:::readable Fir.FuncTraceRuns.isRefinedBy_refl Fir.FuncTraceRuns.isRefinedBy_trans Fir.FuncTraceRuns.isRefinedBy_iff_of_noActs (fingerprint := "14669122733807803638")
*Theorem: refinement of traced functions is a preorder.* It is reflexive
and transitive when refinement of acts and of observations is.

*Theorem: with no act, traced refinement of functions is refinement.*
Traced functions that show no act refine exactly when the functions whose
runs they end as {ref "The-fir-specification--Execution--Refinement"}[refine].
:::

:::readable Fir.FuncTraceRuns.isRefinedBy_iff_world (fingerprint := "5069952568774048")
*Theorem: refinement of traced functions holds for every world.* A target
function refines a source function exactly when, on every argument vector
and at every world, each outcome that the target shows at that world is
allowed by an outcome of the source, which shows the same answers.
:::
