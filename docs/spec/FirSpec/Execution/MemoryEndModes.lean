import VersoManual
import Fir.Execution.MemoryEndModes
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on modes that see the end of a return,
which renders `Fir.Execution.MemoryEndModes` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "Modes that see the end of a return: readable blocks" =>

:::moduleDocs (fingerprint := "18357958049201045590")
:::

:::readable Fir.Func.memEndTree (pin := Fir.TraceState.endOf) (pin := Fir.Memory.Memories.empty) (fingerprint := "3432219675624935408")
*Definition: the tree of a run with memory that sees each return at its
end.* Where the units of the memory $`x` are $`u(x)` bits wide, the memory
numbered $`n` is $`\mu(n)` and addresses are compared by the rule
$`\rho_a`, the tree of the function $`f` of the module $`M` on
$`\vec{v}` with $`k` steps is its run in the state layer over the tree of
choices, from the empty memories, each path that returns the values
$`\vec{w}` with the memories $`S` at its end seen as the end
$`\langle \vec{w}, S, [] \rangle`, with nothing escaped:

$$`\mathrm{tree}^{\mathrm{end}}_{M,f}(\vec{v}, k) = \mathrm{map}_{(r, S) \mapsto \mathrm{end}_S(r)}(\mathrm{run}_{M,f}(\vec{v}, k)(\emptyset))`

where $`\mathrm{end}_S` sees a return of $`\vec{w}` as $`\mathsf{ret}~\langle \vec{w}, S, [] \rangle`
and keeps every other way a path ends. The memories $`S` are those at the
end of the path, after the function's frame has been left.
:::

:::readable Fir.Func.memEndTree_toSet (pin := Fir.Func.memEndRuns) (fingerprint := "9675734803915694836")
*Theorem: the tree has the run with memory, seen at its ends, as its set.*
When the dialect's semantics in the tree denotes its semantics with memory
at the naming $`\rho` with layout entries $`\ell`, for every module
$`M`, function $`f`, arguments $`\vec{v}` and fuel $`k`, the set of
$`\mathrm{tree}^{\mathrm{end}}_{M,f}(\vec{v}, k)` is the run with memory of
$`f` at $`\rho` on $`\vec{v}` at fuel $`k`, each return seen at its end.
The proof is the interpreter's morphism theorem through the layer, at the
empty memories, and the set of a tree keeps mapping a function over its
results.
:::

:::readable Fir.Func.memEndExplore_outcomes Fir.Func.memEndScript_outcomes Fir.Func.memEndExploreNaN_outcomes (pin := Fir.Run.outcomes) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "6416687254847543603")
*Theorems: the modes give the outcomes of the run with memory, seen at
their ends.* With the same hypotheses, let $`R_k` be the run with memory
of $`f` on $`\vec{v}` at fuel $`k`, each return seen at its end. If
exhaustive mode on $`\mathrm{tree}^{\mathrm{end}}_{M,f}(\vec{v}, k)`
with budget $`B` gives the list $`L`, then for every outcome $`o`,

$$`o \in \mathrm{out}(R_k) \iff \exists (\ell, c) \in L.\ \mathrm{path\_end}(\ell) = \mathsf{outcome}~o`

If scripted mode on it, following a sequence that fits, reaches a leaf
whose path ends with the outcome $`o`, then $`o \in \mathrm{out}(R_k)`.
Each outcome that the walk that tries a few NaNs lists is in
$`\mathrm{out}(R_k)`, and when no path it lists made a NaN choice, it
lists every outcome of $`R_k`.
:::

:::readable Fir.Func.traceObservable_of_memEnd (pin := Fir.TOutcome.ofOutcome) (fingerprint := "17507013962650223852")
*Theorem: a return or UB that a mode reports is a traced outcome.* For a
dialect whose ops show no event, a return or UB of the run with memory at
some fuel, each return seen at its end, is an outcome of the function's
traced runs, with an empty trace: its traced behaviour is its behaviour
with memory, each return seen at its end, with an empty trace.
:::
