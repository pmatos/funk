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

:::moduleDocs (fingerprint := "2261672519267001126")
:::

:::readable Fir.TRun Fir.traceObservable (fingerprint := "17724203455732833545")
*Definition: a traced run.* A traced run at one budget is the set of the
ways it may end, each with the trace it showed: a result or a stuck path
after the trace, or UB with its reason after the trace.

*Definition: traced observable behaviour.* For a run $`R_n` at each budget
$`n`, its traced observable behaviour holds:

* $`\mathsf{ret}~t~o` and $`\mathsf{ub}~t~r` when some budget reaches them;
* $`\mathsf{diverge}~t` when there is a budget $`N` such that, at every
  budget $`n`, the run can run out of fuel having shown a prefix of $`t`,
  and $`t` itself when $`N \le n`;
* $`\mathsf{reacts}~T` when, for each $`k`, from some budget on, the run can
  run out of fuel having shown the first $`k` acts of $`T`.

As for M0, reading divergence so assumes that every choice has finitely
many options, so that, by König's lemma, a run that shows more and more of
a trace as its budget grows has one infinite path that shows it.
:::

:::readable Fir.TRun.ofRun Fir.traceObservable_ofRun (fingerprint := "4295895697841493525")
*Definition: a run with no event.* A run of the set monad is a traced run
whose every path shows an empty trace: its UB is UB after no act.

*Theorem: with no event, the traced behaviour is the behaviour.* The traced
observable behaviour of a run with no event is its
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[observable behaviour],
each outcome with an empty trace. Divergence is silent from the start, since
every budget can run out of fuel with an empty trace, and the run shows no
infinite trace.
:::

:::readable Fir.FuncTraceRuns Fir.FuncTraceRuns.IsRefinedBy (pin := Fir.FuncTraceRuns.instHRefinement) (fingerprint := "4035688308089087198")
*Definition: the traced runs of functions.* The traced runs of a function
are its traced run on each argument vector at each budget. A target
function refines a source function when, on every argument vector, its
traced observable behaviour refines the source's.
:::

:::readable Fir.FuncTraceRuns.isRefinedBy_refl Fir.FuncTraceRuns.isRefinedBy_trans (fingerprint := "6050909868132515831")
*Theorem: refinement of traced functions is a preorder.* It is reflexive
and transitive when refinement of acts and of observations is.
:::

:::readable Fir.FuncTraceRuns.ofFuncRuns Fir.FuncTraceRuns.ofFuncRuns_isRefinedBy_iff (fingerprint := "3217292557490457463")
*Definition: functions with no event.* The runs of a function with no event
are traced runs whose every path shows an empty trace.

*Theorem: with no event, traced refinement of functions is refinement.*
Functions with no event refine as traced functions exactly when they
{ref "The-fir-specification--Execution--Refinement"}[refine] as functions,
since their traced behaviours are their behaviours with empty traces.
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

:::readable Fir.Func.traceRuns (pin := Fir.Memory.Memories.empty) (fingerprint := "4633980514941417875")
*Definition: the traced runs of a function.* Where a run names the
dialect's memory $`x` as $`\rho(x)`, whose layout entry is
$`\ell(\rho(x))`, the traced run of the function $`f` of the module $`M` on
$`\vec{v}` with $`k` steps is its run in the traced layer, by the dialect's
semantics there, from no trace and the empty memories. An observer sees the
trace and what it returns.
:::

:::readable Fir.LiftsMem Fir.Func.traceRuns_eq (fingerprint := "9939959716135999148")
*Definition: a dialect whose ops show no event.* A dialect's semantics in
the traced layer lifts its semantics with memory when, at every naming of
its memories, the lift maps each op's semantics with memory to its
semantics in the traced layer.

*Theorem: with no event, traced runs are runs with memory.* The traced runs
of a function of such a dialect are its
{ref "The-fir-specification--Memory--Runs-with-memory"}[runs with memory],
each path with an empty trace, by the interpreter's morphism theorem for
the lift, which keeps frames. So, with the theorem on functions with no
event, every theorem on the refinement of its runs with memory holds of its
traced runs, and tests with no events keep their results.
:::
