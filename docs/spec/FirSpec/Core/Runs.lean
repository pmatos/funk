import VersoManual
import Fir.Core.Runs
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the runs of core functions, which
renders `Fir.Core.Runs` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The runs of core functions: readable blocks" =>

:::readable Fir.Core.funcRuns (pin := Fir.Func.runs) (fingerprint := "10337998491495057787")
*Definition: the runs of a function of a core module.* For a core module
$`M` and a core function $`f`, the runs of $`f` are
$`\mathrm{runs}_M(f)`: on each vector $`v^*` of values of its parameter
types, poison included, and at each budget $`n`, the run
$`\mathrm{runs}_M(f)(v^*)_n` of the
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter], in
the set monad, with $`n` steps of fuel. They are the
{ref "The-fir-specification--Execution--Core-values"}[runs of a core function]
whose observations are the lists of values returned, so the refinement
of core functions is about them.
:::

:::readable Fir.Core.Op.InTracer Fir.Core.InTracer (fingerprint := "9983642069029973491")
*Definition: the tracer subset.* An op is in the _tracer subset_ when it
is $`\mathsf{const}_N~c`, $`\mathsf{add}_N` with neither
$`\mathsf{nuw}` nor $`\mathsf{nsw}`, or $`\mathsf{ret}~t^*`, for any
width $`N`, constant $`c` and types $`t^*`. A core function is in the
tracer subset when every op of every block of it is.

These are the ops of the roadmap's tracer bullet: one tiny program that
went first through every layer of the toolchain, from the IR to the
x86-64 backend. They were the first ops given execution rules, and the
first for which the three obligations were proved.
:::

:::readable Fir.Core.straight_of_tracer (pin := Fir.Func.Straight) (pin := Fir.Core.Op.Valid) (fingerprint := "15143212149356240915")
*Theorem: a valid function of the tracer subset runs straight.* Let $`f`
be a core function that is
{ref "The-fir-specification--Validation--The-general-rules"}[valid] in a
module context and in the tracer subset. Then $`f`
{ref "The-fir-specification--Execution--Progress-and-no-stuck-path"}[runs straight]
to a return: no op of $`f` calls a function, no exit of an op of $`f`
jumps, and each terminator of $`f` has the result types of $`f` as its
operand types.

$`\mathsf{const}` and $`\mathsf{add}` call no function and are not
terminators, and $`\mathsf{ret}` neither calls a function nor jumps. The
only terminator, $`\mathsf{ret}~t^*`, takes operands of the types $`t^*`,
and the {ref "The-fir-specification--Validation--Core-rules"}[core rule]
of $`\mathsf{ret}` asks $`t^*` to be the result types of the function.
:::

:::readable Fir.Core.total_of_tracer (pin := Fir.OpTotal) (fingerprint := "11746737999403355723")
*Theorem: every op of a function of the tracer subset is total.* If the
core function $`f` is in the tracer subset, every op of every block of
$`f` is
{ref "The-fir-specification--Execution--Poison-classes"}[total]: on every
operand vector, its semantics, or its exit for a terminator, has some
outcome. Each of $`\mathsf{const}`, $`\mathsf{add}` with any flags and
$`\mathsf{ret}` is proved total by the obligations of its op family.
:::

:::readable Fir.Core.RunsWell (pin := Fir.FuelMonotone) (pin := Fir.Progress) (pin := Fir.NeverStuck) (fingerprint := "12053394366022874285")
*Definition: a run that runs well.* A run $`R`, given at every budget
$`n` as $`R_n`, _runs well_ when it meets the three obligations of the
section on
{ref "The-fir-specification--Execution--Fuel-and-progress"}[fuel and progress]:

* it is fuel-monotone: for all budgets $`n \le m`, every return and every
  UB of $`R_n` is one of $`R_m`, and every return and every UB of $`R_m`
  is one of $`R_n`, unless $`R_n` may run out of fuel;
* it has progress: at every budget, it has some outcome;
* it has no stuck path: at no budget is a path of it stuck.

It is how this section and the next two state, at once, that a core
function's runs on one argument vector meet all three.
:::

:::readable Fir.Core.tracer_runsWell Fir.Core.tracer_fuelMonotone Fir.Core.tracer_progress Fir.Core.tracer_neverStuck (fingerprint := "3286741478274288802")
*Theorem: every function of the tracer subset in a valid core module runs
well, on every argument vector.* Let $`M` be a
{ref "The-fir-specification--Validation--The-general-rules"}[valid] core
module, $`f` a function of $`M` in the tracer subset, and $`v^*` a vector
of values of the parameter types of $`f`, poison included. Then the runs
$`\mathrm{runs}_M(f)(v^*)` run well, and so each of the three holds on
its own:

* they are fuel-monotone;
* they have progress;
* they have no stuck path.

Fuel monotonicity holds for
{ref "The-fir-specification--Execution--The-runs-of-a-function___-and-fuel-monotonicity"}[every function].
The other two follow from the theorems on functions that run straight,
with the two theorems above.
:::
