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

:::moduleDocs (fingerprint := "11902575432533740743")
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

:::readable Fir.Module.memOps_notUB Fir.Module.memOps_clean (pin := Fir.NoUB) (pin := Fir.Func.memOps) (fingerprint := "16437460514696067429")
*Theorems: the ops of a function leave out what its summary leaves out,
with memory.* Let every function of $`M` be valid, and let $`s` name the
function $`f` of $`M`. Run its ops with memory, in the state layer over the
set monad, from any of its ops on, from any memories, at any budget:

* if $`\mathsf{mayUB} \notin \mathrm{sum}_M(s)`, and each valid op that
  runs by its own rule and leaves out may-UB never ends in UB from any
  memories, no run ends in UB;
* if $`\mathsf{mayPoison} \notin \mathrm{sum}_M(s)`, the environment is
  clean, and each valid op with no callee that leaves out may produce
  poison gives no poison on operands with none, from any memories, every
  list of values that the run returns is clean.

The proof is by induction on the budget, for every function of $`M` at
once, from any memories, one
{ref "The-fir-specification--Memory--The-ways-a-step-with-memory-goes-on"}[step with memory]
at a time. An op that runs by its own rule leaves out each effect that the
summary leaves out, so the hypothesis covers it. A call runs its callee,
whose summary is below its caller's, with less fuel, from the memories its
caller reached with a new frame entered, so the induction covers the
callee's run, recursion included. For poison, the run keeps its
environment clean.
:::

:::readable Fir.Module.summary_neverUB Fir.Module.summary_noPoison (pin := Fir.LawfulDialectEffects) (pin := Fir.Func.memRuns) (fingerprint := "5030757686762725077")
*Theorems: function summaries are sound.* Let the dialect be lawful in
its effects, every function of the module $`M` valid, and $`s` name the
function $`f` of $`M`. Wherever a run names the dialect's memories, with
any layout entries, for every budget of fuel, of the
{ref "The-fir-specification--Memory--Runs-with-memory"}[runs with memory]
of $`f`:

* if $`\mathsf{mayUB} \notin \mathrm{sum}_M(s)`, no run of $`f` ends in
  UB;
* if $`\mathsf{mayPoison} \notin \mathrm{sum}_M(s)`, a run of $`f` on
  arguments with no poison returns no poison.

The obligations of a dialect lawful in its effects speak of each op's
semantics with memory, so they give the hypotheses of the previous
theorems, and no semantics in the set monad is asked for: an op that
touches memory is covered too. A pass may rely on a summary as it relies
on an op's effects (ADR-2026-11-09-1541).
:::
