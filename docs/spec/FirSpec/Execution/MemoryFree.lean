import VersoManual
import Fir.Execution.MemoryFree
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on touching no memory, which renders
`Fir.Execution.MemoryFree` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Touching no memory: readable blocks" =>

:::moduleDocs (fingerprint := "12564574086854445638")
:::

:::readable Fir.Effects.TouchesNoMemory Fir.Effects.TouchesNoMemory.of_le (pin := Fir.Effects) (pin := Fir.Effects.Le) (fingerprint := "10653422458642567564")
*Definition and theorem: a set of effects that touches no memory.* A set of
{ref "The-fir-specification--Execution--Effect-sets"}[effects] $`E` touches
no memory when, for every memory $`x`, $`E` reads, writes and allocates in
no $`x`. A set of effects below one that touches no memory touches none.
:::

:::readable Fir.SymbolTable.ReachesNoMemory Fir.SymbolTable.ReachesNoMemory.of_summary Fir.SymbolTable.ReachesNoMemory.own Fir.SymbolTable.ReachesNoMemory.callee (pin := Fir.SymbolTable.reach) (pin := Fir.SymbolTable.summary) (fingerprint := "14307947686334129542")
*Definition and theorems: a function that reaches no memory.* The function
of a symbol table named by $`s` reaches no memory when every function that
the walk from $`s` reaches, $`s`'s own included, declares no memory effect
for any of its ops. The walk follows only calls that name functions of the
table: a call to any other symbol is stuck, so it reaches nothing.

* A function whose
  {ref "The-fir-specification--Execution--Function-summaries"}[summary]
  touches no memory reaches no memory: the summary holds what a caller sees
  of every op of every function it reaches. The converse fails for a call
  that names no function of the table, which adds every effect to the
  summary.
* Each op of a function that reaches no memory declares no memory effect,
  and each function that it calls reaches no memory, since that function
  reaches nothing that its caller does not.
:::

:::readable Fir.IgnoresMemory Fir.IgnoresMemory.lift Fir.IgnoresMemory.map (fingerprint := "15015104479317298164")
*Definition and theorems: a computation that ignores the memories.* A
computation $`c` in the state layer ignores the memories when, for all
memories $`S` and $`T`:

* if $`c` from $`S` may end in UB for the reason $`r`, then from $`T` it
  may too;
* if $`c` from $`S` may end with the results $`a` and the memories $`S'`,
  then $`S' = S`, and $`c` from $`T` may end with $`a` and $`T`.

A computation of the set monad run in the state layer ignores the memories,
since it keeps them, and mapping the results of a computation that ignores
them keeps it so.
:::

:::readable Fir.OpsIgnoreMemory (pin := Fir.OwnRuleHas) (fingerprint := "12465036732790656999")
*Definition: ops that ignore the memories where they touch none.* The ops
of a dialect ignore the memories where they touch none, in a semantics with
memory, when each op that is a terminator or has no callee, and that
declares no memory effect, ignores the memories on every operand vector: by
its meaning when it is not a terminator, and by its exit when it is. The
{ref "The-fir-specification--Memory--Memory-obligations"}[memory obligations]
do not give it: they compare runs from memories with the same allocations
only, and say nothing of the frames.
:::

:::readable Fir.Ev.notStuck_ok Fir.Ev.notStuck_ub Fir.Ev.mapRet Fir.atMemSteps Fir.atMem Fir.Ev.NotStuck.mapRet Fir.Ev.dropLeft_mapRet (pin := Fir.Ev.NotStuck) (pin := Fir.Ev.dropLeft) (fingerprint := "8601504947282469443")
*Definitions and theorems: a path with other memories.* A path that ends
with a result, or in UB, is not stuck. A path of a run can have the
memories it returns replaced: a return of $`((\vec{w}, S), k)` from a run
of ops becomes $`((\vec{w}, T), k)`, and a return of $`(\vec{w}, S)` from a
run of a function becomes $`(\vec{w}, T)`; every other path is kept. A path
that is not stuck stays so, and dropping the steps a run leaves commutes
with the replacement.
:::
