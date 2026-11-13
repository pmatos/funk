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

:::moduleDocs (fingerprint := "9786552517512518637")
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

:::readable Fir.Core.straight_of_tracer (pin := Fir.Func.Straight) (pin := Fir.Core.Op.Valid) (pin := Fir.Core.Op.callTarget?) (pin := Fir.Core.Op.isTerminator) (pin := Fir.Core.Op.exit?) (pin := Fir.Core.retExit) (pin := Fir.Core.Op.sig) (fingerprint := "15408062743888925642")
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

It is how the
{ref "The-fir-specification--Memory--Core-functions-with-memory"}[section on core functions with memory]
states, at once, that a core function's runs with memory on one argument
vector meet all three.
:::
