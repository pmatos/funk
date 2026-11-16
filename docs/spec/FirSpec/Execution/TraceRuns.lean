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

:::moduleDocs (fingerprint := "10984902927926267901")
:::

:::readable Fir.Step Fir.Step.acts Fir.Step.actsOf Fir.Step.upTo (fingerprint := "16348020394944248890")
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

:::readable Fir.TRun Fir.traceObservable (fingerprint := "14182333727563098907")
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

:::readable Fir.DialectTrace Fir.DialectTrace.Acts (pin := Fir.instHRefinementEvent) (fingerprint := "13213360322648667420")
*Definition: a dialect's events.* A dialect says what its events and the
world's answers are, how one event refines another, and gives each op a
semantics in the traced layer, wherever a run names its memories, as its
semantics with memory does in the state layer. Its acts are its events with
their answers.
:::

:::readable Fir.TraceM.tick Fir.DialectTrace.stepAt (fingerprint := "6008828924152678606")
*Definition: marking the steps.* A step shows $`[\mathsf{tick}]` and
changes nothing else. In the traced layer of marked traces, each op of the
dialect shows a step, then runs by the dialect's rule, each act of its
traces an act of the marked trace.
:::

:::readable Fir.Func.traceRuns Fir.Func.run_eraseSteps (pin := Fir.Memory.Memories.empty) (fingerprint := "574266576010869110")
*Definition: the traced runs of a function.* Where a run names the
dialect's memory $`x` as $`\rho(x)`, whose layout entry is
$`\ell(\rho(x))`, the traced run of the function $`f` of the module $`M` on
$`\vec{v}` with $`k` steps is its run in the traced layer of marked traces,
from the empty memories. An observer sees the acts of the trace and what it
returns.

*Theorem: erasing the steps.* Mapping each step to no act and each act to
itself maps the traced run of a function to its run in the traced layer by
the dialect's rules alone, by the interpreter's morphism theorem: the image
of a step followed by an op's rule is the rule.
:::

:::readable Fir.LiftsMem Fir.Func.traceRuns_noActs Fir.Func.traceObservable_traceRuns (fingerprint := "189810853174328088")
*Definition: a dialect whose ops show no event.* A dialect's semantics in
the traced layer lifts its semantics with memory when, at every naming of
its memories, the lift maps each op's semantics with memory to its
semantics in the traced layer.

*Theorem: with no event, traced runs are runs with memory.* The traced runs
of a function of such a dialect show no act and end as its
{ref "The-fir-specification--Memory--Runs-with-memory"}[runs with memory]:
erasing their steps gives the lift of those runs. So its traced observable
behaviour is its observable behaviour with memory, each outcome with an
empty trace, and every theorem on the refinement of its runs with memory
holds of its traced runs. Tests with no events keep their results.
:::
