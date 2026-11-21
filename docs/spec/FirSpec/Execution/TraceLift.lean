import VersoManual
import Fir.Execution.TraceLift
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the traced runs of a dialect with no event, which renders
`Fir.Execution.TraceLift` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Traced runs of a dialect with no event: readable blocks" =>

:::moduleDocs (fingerprint := "10762966644135900264")
:::

:::readable Fir.DialectTrace.ofMem Fir.DialectTrace.ofMem_liftsMem (fingerprint := "58147739265247047")
*Definition: the traced semantics of a dialect with no event.* A dialect
whose ops show no event has, as its
{ref "The-fir-specification--Memory--A-dialect___s-traced-runs"}[traced semantics],
no event, one answer, and each op's semantics with memory at $`\ell`,
$`\rho` and $`L`, lifted onto the memories of the traced state: it shows
nothing and keeps what escaped.

*Theorem: it lifts the semantics with memory.* So the lift onto the
memories of the traced state maps each op's semantics with memory to its
traced semantics, by definition, at every naming of its memories and all
items a run gives each op.
:::

:::readable Fir.End.isRefinedBy_of_mem (fingerprint := "165268049498222231")
*Theorem: memories that refine others give ends that refine each other.*
When refinement of the returned values is transitive:

$$`\vec{v} \sqsubseteq \vec{v}' \land S \sqsubseteq S' \implies \langle \vec{v}, S, E\rangle \sqsubseteq \langle \vec{v}', S', E\rangle`

The identity renaming shows the first end in the second. Memories that
refine each other have the same allocations, each of the same kind,
alignment, liveness, size and address, so the address rule relates them,
and a live allocation's units refine the other's. A dangling pointer is
seen as poison, which every value refines.
:::

:::readable Fir.Result.memEnd Fir.Func.memEndRuns_eq Fir.SetM.map_iff (fingerprint := "14736022310476980214")
*Definition: the end of a run from given memories.* A path of a run from
given memories that returns $`(\vec{v}, S)` is seen as returning the end
$`\langle \vec{v}, S, []\rangle`, with nothing escaped; a path out of
fuel or stuck is seen as it is.

*Theorem: the runs with memory, seen at each end, are the runs from the
memories a run starts with.* The runs with memory of a function, each
return seen at its end, are its runs from $`\mathrm{start}(L)`, each path
seen so. A
computation of the set monad whose results are mapped by $`g` ends with
$`g(a)` for each result $`a`, or with its UB.
:::

:::readable Fir.Func.memEndRuns_ret_iff Fir.Func.memEndRuns_ub_iff Fir.Func.memEndRuns_exhausted_iff (fingerprint := "10208948591819177243")
*Theorems: the outcomes of the runs with memory, seen at each end.* At
each budget, a run with memory returns the end $`\langle \vec{v}, S,
E\rangle` exactly when $`E = []` and the run from $`\mathrm{start}(L)`
returns $`(\vec{v}, S)`; it hits UB, or runs out of fuel, exactly when the
run from $`\mathrm{start}(L)` does.
:::

:::readable Fir.Func.memEndRuns_isRefinedBy_of_from Fir.Func.traceRuns_isRefinedBy_of_from (fingerprint := "8335039658620344789")
*Theorem: refinement from the memories a run starts with gives traced
refinement.* When the refinement of values is transitive, and the
behaviour of $`f` on $`\vec{v}` from $`\mathrm{start}(L)`, the memories
it ends with included, is
refined by that of $`f'` on $`\vec{v}'` in $`M'`:

* the behaviour with memory of $`f`, each return seen at its end, is
  refined by that of $`f'`: a return of $`(\vec{v}', S')` is allowed by
  UB, or by a return of $`(\vec{v}, S)` with $`\vec{v} \sqsubseteq
  \vec{v}'` and $`S \sqsubseteq S'`, whose end refines by the theorem
  above;
* for a dialect whose ops show no event, the traced behaviour of $`f` is
  refined by that of $`f'`: both are these behaviours with empty traces.
:::
