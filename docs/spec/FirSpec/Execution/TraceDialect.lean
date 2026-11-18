import VersoManual
import Fir.Execution.TraceDialect
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a dialect's traced runs, which renders
`Fir.Execution.TraceDialect` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "A dialect's traced runs: readable blocks" =>

:::moduleDocs (fingerprint := "6866759415476710901")
:::

:::readable Fir.DialectTrace Fir.DialectTrace.Acts (pin := Fir.instHRefinementEvent) (fingerprint := "9904479323341056526")
*Definition: a dialect's events.* A dialect says what its events and the
world's answers are, how one event refines another, and gives each op a
semantics in the traced layer, wherever a run names its memories and
whatever items it gives each op, as its semantics with memory does in the
state layer. Its acts are its events with
their answers.
:::

:::readable Fir.TraceM.tick Fir.DialectTrace.stepAt (fingerprint := "15622607650213344749")
*Definition: marking the steps.* A step shows $`[\mathsf{tick}]` and
changes nothing else. In the traced layer of marked traces, each op that
runs by the dialect's rule, a terminator among them, shows a step, then
runs by that rule, each act of its traces an act of the marked trace. A
call shows no step of its own: the ops of its callee show theirs.
:::

:::readable Fir.Func.traceRuns Fir.Func.run_eraseSteps (pin := Fir.Memory.Memories.empty) (fingerprint := "18372342297826570772")
*Definition: the traced runs of a function.* Where a run names the
dialect's memory $`x` as $`\rho(x)`, whose layout entry is
$`\ell(\rho(x))`, and gives each op the items $`L`, the traced run of the
function $`f` of the module $`M` on $`\vec{v}` with $`k` steps is its run in
the traced layer of marked traces, by the dialect's semantics in the traced
layer at $`\ell`, $`\rho` and $`L`, from the empty memories. An observer sees the acts of the trace and what it
returns.

*Theorem: erasing the steps.* Mapping each step to no act and each act to
itself maps the traced run of a function to its run in the traced layer by
the dialect's rules alone, by the interpreter's morphism theorem: the image
of a step followed by an op's rule is the rule.
:::

:::readable Fir.LiftsMem Fir.Func.traceRuns_noActs Fir.Func.traceObservable_traceRuns (fingerprint := "12106958622849886657")
*Definition: a dialect whose ops show no event.* A dialect's semantics in
the traced layer lifts its semantics with memory when, at every naming of
its memories and all items a run gives each op, the lift maps each op's semantics with memory to its
semantics in the traced layer.

*Theorem: with no event, traced runs are runs with memory.* The traced runs
of a function of such a dialect show no act and end as its
{ref "The-fir-specification--Memory--Runs-with-memory"}[runs with memory]:
erasing their steps gives the lift of those runs. So its traced observable
behaviour is its observable behaviour with memory, each outcome with an
empty trace, and every theorem on the refinement of its runs with memory
holds of its traced runs. So a dialect whose traced semantics lifts its
semantics with memory keeps the results of its tests.
:::
