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

:::moduleDocs (fingerprint := "9844489512117009611")
:::

:::readable Fir.Func.mem_allOps Fir.Func.enter_ops Fir.Operation.call?_of (fingerprint := "11322144752609607633")
*Theorems: the ops that a run runs.* An op of a block of a function is
one of its ops at any depth. A function that starts its run starts with
the ops of one of its blocks, with its parameters bound to its arguments.
An op that is not a terminator and has the callee $`c` calls $`c`.
:::

:::readable Fir.Func.memCall_ub Fir.Func.memCall_ret Fir.Module.memOps_notUB Fir.Module.memOps_clean (pin := Fir.NoUB) (pin := Fir.Func.memOps) (fingerprint := "11432641747953504554")
*Theorems: the ops of a function leave out what its summary leaves out,
with memory.* A run in a call's frame hits UB only where its ops, run from
the memories with a frame entered, hit UB, and returns what they return,
with the frame left. Let every function of $`M` be valid, and let $`s` name the
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

:::readable Fir.Module.summary_neverUB_from Fir.Module.summary_noPoison_from (pin := Fir.Func.memRunsFrom) (fingerprint := "5508738324192612352")
*Theorems: function summaries are sound from given memories.* Under the
hypotheses of the previous theorems, the same holds of the
{ref "The-fir-specification--Memory--Runs-from-given-memories"}[runs of $`f` from given memories],
from any memories $`S`: if $`\mathsf{mayUB} \notin \mathrm{sum}_M(s)`, no
run ends in UB, and if $`\mathsf{mayPoison} \notin \mathrm{sum}_M(s)`, a
run on arguments with no poison returns no poison. A call runs its callee
so, from the memories its caller reached, so a pass may rely on a callee's
summary at each call.
:::
