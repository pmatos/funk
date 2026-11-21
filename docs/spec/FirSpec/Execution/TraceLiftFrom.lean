import VersoManual
import Fir.Execution.TraceLiftFrom
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on traced runs from a traced state of a dialect with no
event, which renders `Fir.Execution.TraceLiftFrom` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build fails when the
Lean changes under it.
-/

#doc (Manual) "Traced runs from a traced state, for a dialect with no event: readable blocks" =>

:::moduleDocs (fingerprint := "1277147490547063446")
:::

:::readable Fir.Result.withEscaped (fingerprint := "16909940391715339000")
*Definition: a run from memories, read from a traced state.* A path of a
run from the memories of the traced state $`s` is read from $`s`: a return
$`(\vec{v}, S)` returns $`(\vec{v}, s[\mathrm{mem} := S])`, the traced
state with the memories it ends with and the allocations $`s` lets escape;
a path out of fuel or stuck stays so.
:::

:::readable Fir.Func.traceRunsFrom_noActs_ofMem (fingerprint := "2365568065659706682")
*Theorem: traced runs from a traced state show no act.* For a dialect whose
ops show no event, with the lifted traced semantics, at every budget $`n`,
the traced run of $`f` from the traced state $`s` on $`\vec{v}` shows no
act, and its paths end as those of the run of $`f` from the memories of
$`s`, read from $`s`. Erasing the steps of the traced run gives its run in
the traced layer by the dialect's rules alone, and lifting the run with
memory gives the same, since each op's traced semantics is its lift by
definition. So the proof needs no `LiftsMem`.
:::

:::readable Fir.Result.withEscaped_ret_iff Fir.Result.withEscaped_ub_iff Fir.Result.withEscaped_exhausted_iff (fingerprint := "15095899425654975367")
*Theorems: the outcomes of a run read from a traced state.* A run from the
memories of $`s`, read from $`s`, returns $`(\vec{v}, s_1)` exactly when
$`s_1 = s[\mathrm{mem} := S]` for a return $`(\vec{v}, S)` of the run; it
hits UB, or runs out of fuel, exactly when the run does.
:::

:::readable Fir.Func.traceRunsFrom_isRefinedBy_of_memRunsFrom (fingerprint := "14512304885179745568")
*Theorem: from runs with memory to traced runs from a traced state.* For a
dialect whose ops show no event, with the lifted traced semantics, and every
traced state $`s`:

$$`\mathrm{runs}(f, \vec{v}, s.\mathrm{mem}) \sqsubseteq \mathrm{runs}(f', \vec{v}', s.\mathrm{mem}) \implies \mathrm{traceRuns}(f, \vec{v}, s) \sqsubseteq \mathrm{traceRuns}(f', \vec{v}', s)`

the traced state each return ends in included. Both traced runs show no
act, so their traced behaviours are their behaviours with memory, read from
$`s`, with an empty trace; both returns keep the allocations $`s` lets
escape, so the end states refine when the memories do. This is the bridge
by which the core and CoreGpu take their hypothesis of congruence in the
callee, stated with memory, to the one that the traced layer's own theorem
asks.
:::
