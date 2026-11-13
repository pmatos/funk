import VersoManual
import Fir.Execution.MemoryFreeRuns
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on runs that touch no memory, which
renders `Fir.Execution.MemoryFreeRuns` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Runs that touch no memory: readable blocks" =>

:::moduleDocs (fingerprint := "13870372205624324422")
:::

:::readable Fir.Func.memCall_ignoresMemory (pin := Fir.Func.memCall) (fingerprint := "4038606851964616677")
*Theorem: a call's frame keeps memories that its ops ignore.* When the run
of a callee's ops from $`\mathrm{enter}(S)` ignores the memories, so does
the run in the call's frame from $`S`: each return of the ops ends with
$`\mathrm{enter}(S)`, and leaving the frame gives back $`S`.
:::

:::readable Fir.Module.memOps_ignoresMemory (pin := Fir.Func.memOps) (pin := Fir.OpsIgnoreMemory) (fingerprint := "4956512854030440429")
*Theorem: runs of a function that touches no memory ignore the memories.*
Let the ops of the dialect ignore the memories where they touch none. Let
$`f` be the function of $`M` with the symbol $`s`, which reaches no
memory. Then every run with memory of ops of $`f`, from any of
its ops on, at every budget, that ends from the memories $`S` in a way that
is not stuck, returns $`S` if it returns, and ends the same way from any
memories $`T`, with $`T` in place of $`S`. Calls and recursion are
included.

The proof is by induction on the fuel, op by op. An op that runs by its own
rule declares no memory effect, since $`f` reaches no memory, so it ignores
the memories. A call runs its callee, which reaches nothing that $`f` does
not, in a frame, from the memories $`f` reached; the callee's run has
less fuel, so the induction covers it.
:::

:::readable Fir.Func.memRunsFrom_ignoresMemory Fir.Func.memRunsFrom_exhausted_iff (pin := Fir.Func.memRunsFrom) (fingerprint := "1340689679392970907")
*Theorems: a function that touches no memory runs the same from any
memories.* For such a function, every way its run from given memories
$`S` ends that is not stuck returns $`S` if it returns, and the run from
any other memories $`T` ends the same way, with $`T`. So it runs out of fuel
from $`S` at a budget exactly when it does from $`T` at that budget.
:::

:::readable Fir.Func.memRunsFrom_boundedBy_of_finite (pin := Fir.FuncRuns.BoundedBy) (pin := Fir.exists_common_bound) (fingerprint := "5823256181184874863")
*Theorem: finitely many argument vectors bound a function that touches no
memory.* When $`f` reaches no memory and its parameter types
have finitely many argument vectors, one budget $`B` bounds its runs from
given memories: past $`B`, no run of $`f` from any memories runs out of
fuel unless it does at every budget. Each argument vector has its own
budget from the empty memories, finitely many have a largest, and the
memories do not change whether $`f` runs out of fuel.
:::
