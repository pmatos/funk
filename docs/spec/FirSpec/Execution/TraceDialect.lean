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

:::moduleDocs (fingerprint := "4193867457959602704")
:::

:::readable Fir.DialectTrace Fir.DialectTrace.Acts (pin := Fir.instHRefinementEvent) (fingerprint := "16873117125355051426")
*Definition: a dialect's events.* A dialect says what its events and the
world's answers are, how one event refines another, and gives each op a
semantics in the traced layer, on the
{ref "The-fir-specification--Memory--The-world-and-escaped-memory"}[traced state],
wherever a run names its memories and whatever items it gives each op, as
its semantics with memory does in the state layer. Its acts are its events
with their answers.
:::

:::readable Fir.TraceM.tick Fir.DialectTrace.stepAt (fingerprint := "14624120199274421574")
*Definition: marking the steps.* A step shows $`[\mathsf{tick}]` and
changes nothing else. In the traced layer of marked traces, each op that
runs by the dialect's rule, a terminator among them, shows a step, then
runs by that rule, each act of its traces an act of the marked trace. A
call shows no step of its own: the ops of its callee show theirs.
:::

:::readable Fir.TraceState.endOf Fir.Func.traceRuns Fir.Func.observedRuns Fir.Func.run_eraseSteps (pin := Fir.TraceState.init) (fingerprint := "10032265652291617458")
*Definition: the traced runs of a function.* Where a run names the
dialect's memory $`x` as $`\rho(x)`, whose layout entry is
$`\ell(\rho(x))`, and gives each op the items $`L`, the traced run of the
function $`f` of the module $`M` on $`\vec{v}` with $`k` steps is its run in
the traced layer of marked traces, by the dialect's semantics in the traced
layer at $`\ell`, $`\rho` and $`L`, from the empty memories with nothing
escaped. An observer sees the acts of the trace and, at a return of the
values $`\vec{v}'` in the traced state $`(S, E)`, the
{ref "The-fir-specification--Memory--The-end-of-a-return"}[end of the return]
$`\langle \vec{v}', S, E\rangle`, which names the memory numbered $`n` as
$`\mu(n)` and compares addresses by the rule $`r`. The caller gives
$`\mu`, which should name the memory numbered $`n` as $`\rho` names the
dialect's memory of that number: for the core, whose memories are their
numbers, $`\mu = \rho`.

*Definition: the spec's traced runs.* The spec's traced runs of a function
are its traced runs whose ends of returns compare addresses by the rule
$`\mathsf{ignore}`: no address is compared at the end of a return, and an
address is seen only through the integers a run shows. The human ruled this
on 2026-11-20, on #233.

*Theorem: erasing the steps.* Mapping each step to no act and each act to
itself maps the traced run of a function to its run in the traced layer by
the dialect's rules alone, by the interpreter's morphism theorem: the image
of a step followed by an op's rule is the rule.
:::

:::readable Fir.LiftsMem Fir.Func.memEndRuns Fir.Func.traceRuns_noActs Fir.Func.traceObservable_traceRuns (fingerprint := "3468461626948554357")
*Definition: a dialect whose ops show no event.* A dialect's semantics in
the traced layer lifts its semantics with memory when, at every naming of
its memories and all items a run gives each op, the lift onto the memories
of the traced state maps each op's semantics with memory to its semantics
in the traced layer. The runs with memory of a function, each return seen
at its end, are its
{ref "The-fir-specification--Memory--Runs-with-memory"}[runs with memory]
whose returns of $`\vec{v}` with the memories $`S` are seen as
$`\langle \vec{v}, S, []\rangle`.

*Theorem: with no event, traced runs are runs with memory.* The traced runs
of a function of such a dialect show no act, let nothing escape, and end as
its runs with memory, each return seen at its end: erasing their steps
gives the lift of those runs. So its traced observable behaviour is its
observable behaviour with memory, each return seen at its end, each outcome
with an empty trace. When it returns no pointer and nothing escaped, the
{ref "The-fir-specification--Memory--Laws-of-the-end-of-a-return"}[end of its return]
is refined exactly when its returned values are and nothing escaped in the
other, so a dialect whose traced semantics lifts its semantics with memory,
and whose functions return no pointer, keeps the results of its tests.
:::
