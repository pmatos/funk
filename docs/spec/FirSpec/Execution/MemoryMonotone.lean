import VersoManual
import Fir.Execution.MemoryMonotone
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on runs with memory at every budget,
which renders `Fir.Execution.MemoryMonotone` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "Runs with memory at every budget: readable blocks" =>

:::moduleDocs (fingerprint := "3134613195537927620")
:::

:::readable Fir.Result.mapVal Fir.SetM.run_map Fir.LeavesAtMost.mapVal Fir.Ahead.mapVal (fingerprint := "17867899712697039806")
*Definition and theorems: mapping what a run returns.* $`\mathrm{mapVal}_F`
maps the value that a return carries by $`F` and keeps the steps it leaves.
A path of $`f \mathbin{<\$>} s` ends with $`f(a)` for a result $`a` of
$`s`, or where $`s` ends with an error or UB. Mapping keeps a bound on the
steps a run leaves, and keeps one run
{ref "The-fir-specification--Execution--The-runs-of-a-function___-and-fuel-monotonicity"}[ahead]
of another.
:::

:::readable Fir.fromState_bind_result Fir.runFrom_inFrame Fir.Ahead.bindCall (fingerprint := "3396021307234932204")
*Theorems: a call, from given memories.* A run of ops in a call's frame,
from $`S`, runs from $`\mathrm{enter}(S)`, and each of its returns leaves
the frame, $`\mathrm{exit}(S')`. A call followed by what its caller does
with the result is ahead with $`j` more steps of fuel, from the same
memories, when its callee is ahead from any memories and so is what the
caller does with a return that leaves $`j` more steps, from the memories
that return ends with. A callee that runs out of fuel ends its caller so.
:::

:::readable Fir.Func.runOps_memLeft_le Fir.Func.runOps_memAhead (pin := Fir.LeavesAtMost) (pin := Fir.Ahead) (fingerprint := "16258431355073082387")
*Theorems: a run of ops with memory at two budgets.* For every dialect
whose ops have a semantics in the state layer, whatever they do to the
memories, from every memories $`S`: a run of ops with $`n` steps of fuel
leaves at most $`n`, and the run with $`n + j` steps is ahead of it by
$`j`. Each of the smaller run's returns, with the memories it ends with, is
one of the larger run's that leaves $`j` more steps; each return of the
larger is one of the smaller that leaves $`j` fewer steps and ends with the
same memories, unless the smaller can run out of fuel; and the two hit the
same UB. The proof is the one for runs in the set monad, by induction on
the budget, each step from the memories that the step before it ended
with; a call enters a frame from the same memories in both runs.
:::

:::readable Fir.Result.finish Fir.Ahead.finish_up Fir.Ahead.finish_down (fingerprint := "11089897184876704988")
*Definition and theorems: what a function does with its ops' run.* A
function returns what its entry block's ops return, mapped, and runs out of
fuel when they do. When the ops with more fuel are ahead, each return or
UB of the smaller run is one of the larger, and each of the larger is one
of the smaller, unless the smaller can run out of fuel.
:::

:::readable Fir.fromState_fst Fir.Func.run_fromState Fir.Func.run_fromState_stuck (fingerprint := "10140593824667432733")
*Theorems: the run of a function with memory.* What a computation of the
layer may end with from $`S`, without the memories it ends with, is what
it ends with read from $`S`, without them. A function's run with memory from
$`S`, when it starts, is its entry block's ops run from
$`\mathrm{enter}(S)`, finished; when it cannot start, every path of it is
stuck there.
:::

:::readable Fir.Func.memRuns_fuelMonotone (pin := Fir.FuelMonotone) (fingerprint := "17768983793765334376")
*Theorem: runs with memory are fuel-monotone.* For every function of every
module of every dialect, wherever a run names its memories, on every
argument vector, its
{ref "The-fir-specification--Memory--Runs-with-memory"}[runs with memory]
are fuel-monotone, calls included, whatever its ops do to the memories:
more fuel never changes how a run with memory that returns or hits UB
ends.
:::
