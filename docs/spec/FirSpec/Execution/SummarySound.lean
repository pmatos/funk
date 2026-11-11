import VersoManual
import Fir.Execution.SummarySound
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on sound function summaries, which
renders `Fir.Execution.SummarySound` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Function summaries are sound: readable blocks" =>

:::moduleDocs (fingerprint := "7652720213210074280")
:::

:::readable Fir.DVals.Clean Fir.Env.Clean (fingerprint := "8528918267713506938")
*Definition: values with no poison.* A list of values is _clean_ when no
value of it is poison, and an environment is clean when no value it binds
is.
:::

:::readable Fir.HVector.clean_toDVals Fir.mem_of_lookup Fir.Env.Clean.value Fir.Env.Clean.bind Fir.Env.Clean.mapM_value Fir.Env.Clean.operands (pin := Fir.HVector.Any) (fingerprint := "3442109685904206130")
*Theorems: a clean environment gives clean values.* The values of an
operand vector are clean exactly when no element of it is poison. A name
that a list looks up is bound in it, so a value that a clean environment
binds is not poison, and neither are the values or the operands found in
it. Binding clean values in a clean environment leaves it clean.
:::

:::readable Fir.Func.mem_allOps Fir.Func.enter_ops Fir.Operation.call?_of (fingerprint := "11322144752609607633")
*Theorems: the ops that a run runs.* An op of a block of a function is
one of its ops at any depth. A function that starts its run starts with
the ops of one of its blocks, with its parameters bound to its arguments.
An op that is not a terminator and has the callee $`c` calls $`c`.
:::

:::readable Fir.Module.runOps_notUB Fir.Module.runOps_clean (pin := Fir.LawfulDialectEffects) (fingerprint := "9643212442418999716")
*Theorems: the ops of a function leave out what its summary leaves out.*
Let the dialect be lawful in its effects, and every function of $`M`
valid. Let $`s` name the function $`f` of $`M`. From any ops of the blocks
of $`f`, at any budget:

* if $`\mathsf{mayUB} \notin \mathrm{sum}_M(s)`, no run ends in UB;
* if $`\mathsf{mayPoison} \notin \mathrm{sum}_M(s)` and the environment is
  clean, every list of values that the run returns is clean.

The proof is by induction on the budget. An op that runs by its own rule
leaves out each effect that the summary leaves out, so the obligations of
a lawful dialect cover it. A call runs its callee, whose summary is below
its caller's, with less fuel, so the induction covers the callee's run,
recursion included. For poison, the run keeps its environment clean.
:::

:::readable Fir.Module.summary_neverUB Fir.Module.summary_noPoison (fingerprint := "15916412028685664532")
*Theorems: function summaries are sound.* Let the dialect be lawful in
its effects, every function of the module $`M` valid, and $`s` name the
function $`f` of $`M`. For every budget of fuel:

* if $`\mathsf{mayUB} \notin \mathrm{sum}_M(s)`, no run of $`f` ends in
  UB;
* if $`\mathsf{mayPoison} \notin \mathrm{sum}_M(s)`, a run of $`f` on
  arguments with no poison returns no poison.

A pass may rely on a summary as it relies on an op's effects
(ADR-2026-11-10-2108).
:::
