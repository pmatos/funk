import VersoManual
import Fir.Execution.MemoryCalls
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on runs from given memories, which
renders `Fir.Execution.MemoryCalls` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Runs from given memories: readable blocks" =>

:::moduleDocs (fingerprint := "3237605153120205651")
:::

:::readable Fir.Result.withMem Fir.Result.finish_id_run (pin := Fir.Result.finish) (pin := Fir.Ev.dropLeft) (fingerprint := "9590645358696005234")
*Definition and theorem: a run's end, with its memories.* A way a
function's run ends, read with the memories it ends with, carries them on a
return, and shows none when it runs out of fuel. A path of a run of ops,
finished, is a path of the run without the steps it leaves.
:::

:::readable Fir.Func.memCall_eq Fir.Func.memCall_ahead Fir.Func.memCall_left_le Fir.Func.memOps_exhausted_down (pin := Fir.Ahead) (pin := Fir.LeavesAtMost) (fingerprint := "13402143546999899124")
*Theorems: a run in a call's frame, at every budget.* A run in a call's
frame from $`S` is the run of its ops from $`\mathrm{enter}(S)`, each
return $`((\vec{w}, T), k)` leaving the frame as
$`((\vec{w}, \mathrm{exit}(T)), k)`. So, as the run of its ops, it gives
back at most the fuel it was given, and with $`j` more steps of fuel it is
ahead of the run with fewer. A run with memory that runs out of fuel with
$`j` more steps runs out of fuel with fewer, from the same memories: it
takes the same path, and runs out sooner.
:::

:::readable Fir.Func.memRunsFrom Fir.Func.memRunsFrom_enter Fir.Func.memRunsFrom_run (pin := Fir.Func.run) (fingerprint := "11164435814742632482")
*Definition and theorems: the runs of a function from given memories.* The
runs of $`f` of $`M` from given memories are its runs with memory, on each
argument vector $`\vec{v}` and from each memories $`S`, at each budget, each
return carrying the values it returns and the memories it ends with:

$$`\mathrm{runs}^S_{M,f}(\vec{v}, S)(k) = \mathrm{run}_{M,f}(\vec{v}, k) \mathbin{@} S`

When $`f` starts on $`\vec{v}` at its entry block's ops $`b^*` in the
environment $`E`, its run from $`S` is
$`\mathrm{call}_M(k, f, E, b^*) \mathbin{@} S`, finished: a call's run in its
frame, without the steps it leaves. When $`f` does not start, every path
is stuck.
:::

:::readable Fir.Func.memRunsFrom_fuelMonotone Fir.Func.memRunsFrom_exhausted_down (pin := Fir.FuelMonotone) (fingerprint := "8569150336907149035")
*Theorems: runs from given memories at every budget.* The runs of every
function from given memories are fuel-monotone, as the runs with memory
are ({ref "The-fir-specification--Memory--Runs-with-memory-at-every-budget"}[runs with memory at every budget]),
and one that runs out of fuel runs out of fuel with fewer steps.
:::

:::readable Fir.Func.memRuns_isRefinedBy_of_from (pin := Fir.Func.memRuns) (fingerprint := "13660275553821939867")
*Theorem: runs with memory refine when runs from the empty memories do.*
The {ref "The-fir-specification--Memory--Runs-with-memory"}[runs with memory]
of a function are its runs from the empty memories, with the memories they
end with dropped. So when the behaviour of $`f'` in $`M'` from the empty
memories refines that of $`f` in $`M`, values and memories, the behaviour
with memory of $`f'` refines that of $`f`:

$$`\mathrm{obs}(\mathrm{runs}^S_{M,f}(\vec{v}, \varnothing)) \sqsubseteq \mathrm{obs}(\mathrm{runs}^S_{M',f'}(\vec{v}', \varnothing)) \implies \mathrm{obs}(\mathrm{runs}^{\mathrm{mem}}_{M,f}(\vec{v})) \sqsubseteq \mathrm{obs}(\mathrm{runs}^{\mathrm{mem}}_{M',f'}(\vec{v}'))`
:::
