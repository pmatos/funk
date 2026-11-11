import VersoManual
import Fir.Execution.MemoryRuns
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on runs with memory, which renders
`Fir.Execution.MemoryRuns` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Runs with memory: readable blocks" =>

:::moduleDocs (fingerprint := "1985518580704619510")
:::

:::readable Fir.MonadMorphism.liftState Fir.MonadMorphism.liftState_mapsFrame (fingerprint := "8015592493867984939")
*Definition: a computation with no memory, in the layer.* For a lawful
monad $`m`, a computation $`x` of $`m` runs in the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] by
keeping the state: $`\mathrm{lift}(x)(S) = \mathrm{map}_{a \mapsto (a, S)}(x)`.
This is a monad morphism from $`m` to the layer over it.

*Theorem: lifting keeps frames.* When a frame of $`m` is the computation
itself, as in the set monad, lifting keeps frames: entering a call and
leaving it at once gives back the memories,
$`\mathrm{exit}(\mathrm{enter}(S)) = S`.
:::

:::readable Fir.DialectDenote.liftState Fir.DialectDenote.liftState_mapsDenote (fingerprint := "1253374098376535126")
*Definition: a semantics with no memory, in the layer.* A dialect whose
ops have their semantics in $`m` has one in the state layer over $`m`:
each op runs by its rule in $`m` and keeps the memories,
$`\mathrm{denote}_o(\vec{v}) = \mathrm{lift}(\mathrm{denote}^m_o(\vec{v}))`
and the same for $`\mathrm{exit}_o`. Lifting keeps this semantics, by its
definition.
:::

:::readable Fir.Func.memRuns (pin := Fir.Memory.Memories.empty) (fingerprint := "15150550198120477738")
*Definition: the runs with memory of a function.* For memories named by
$`X` with units of $`u(x)` bits, and a dialect whose ops have their
semantics in the state layer over the set monad, the run with memory of
the function $`f` of the module $`M` on $`\vec{v}` with $`k` steps is its
run in that layer, from the empty memories. An observer sees what it
returns, not the memories it ends with, until observations at the end of
a run are designed (#233). So the runs with memory of a function are
runs in the sense of the
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[outcomes],
and refinement, fuel monotonicity and progress speak of them.
:::

:::readable Fir.Func.memRun_eq Fir.Func.memRuns_eq (fingerprint := "16364906903141416714")
*Theorem: with no memory touched, a run with memory is a run.* For a
dialect whose semantics in the layer is its semantics in the set monad,
lifted, the run with memory of every function from any memories $`S` is
its run in the set monad, each path keeping $`S`:

$$`\mathrm{run}^{\mathrm{mem}}_{M,f}(\vec{v}, k)(S) = \mathrm{map}_{r \mapsto (r, S)}(\mathrm{run}_{M,f}(\vec{v}, k))`

So its runs with memory are its runs. The proof is the
{ref "The-fir-specification--Execution--Monad-morphisms"}[interpreter's morphism theorem]
for the lift, which keeps each op's semantics and keeps frames.
:::

:::readable Fir.Func.memRuns_fuelMonotone Fir.Func.memProgress_of_lawful (fingerprint := "5638091794242595549")
*Theorem: fuel monotonicity and progress, with memory.* For a dialect
whose ops touch no memory, the runs with memory of every function of
every module are fuel-monotone. When the dialect is lawful for poison and
every function of the module is valid and runs within the module, a run
with memory has an outcome at every budget.
:::

:::readable Fir.Func.memRuns_args_isRefinedBy_of_lawful Fir.Func.memRuns_replaceBody_isRefinedBy_of_lawful (fingerprint := "7818164282470471330")
*Theorem: refinement, with memory.* For a lawful dialect whose ops touch
no memory, in a module whose functions are all valid: a function's
behaviour with memory on arguments that refine others refines its
behaviour with memory on those others; and replacing the body of a
function with one that refines it with memory refines every function of
the module with memory, under the conditions of the theorem on runs.
:::
