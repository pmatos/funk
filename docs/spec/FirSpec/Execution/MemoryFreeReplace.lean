import VersoManual
import Fir.Execution.MemoryFreeReplace
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on congruence in a callee that touches no
memory, which renders `Fir.Execution.MemoryFreeReplace`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Congruence in a callee that touches no memory: readable blocks" =>

:::moduleDocs (fingerprint := "1207515622167629784")
:::

:::readable Fir.Func.memRunsFrom_ret_iff Fir.Func.memRunsFrom_ub_iff Fir.Func.memRunsFrom_exhausted_iff_memRuns (pin := Fir.Func.memRuns) (fingerprint := "3525218910041995322")
*Theorems: runs from given memories are runs with memory.* Let the ops of
the dialect ignore the memories where they touch none, at a layout and
naming of its memories, and let $`f` reach no memory. Then
at every budget and from every memories $`S`, the run of $`f` from $`S`
returns $`(\vec{w}, S')` exactly when $`S' = S` and its
{ref "The-fir-specification--Memory--Runs-with-memory"}[run with memory]
returns $`\vec{w}`, and hits UB, or runs out of fuel, exactly when its run
with memory does.
:::

:::readable Fir.Func.memRunsFrom_isRefinedBy_of_memRuns (fingerprint := "6732269954989396360")
*Theorem: refinement with memory is refinement from given memories, for
functions that touch no memory.* When $`f` in $`M` and $`f` with a new
body in $`M'` both reach no memory, and the second refines
the first with memory, it refines it from given memories too, the memories
they end with included: from $`S`, both end with $`S`, which refines
itself.
:::

:::readable Fir.Func.memRuns_replaceBody_isRefinedBy_of_finite Fir.Func.memRuns_replaceBody_isRefinedBy_of_memRuns (pin := Fir.LawfulDialectMonotone) (fingerprint := "8613120408715234675")
*Theorems: congruence in the callee, with no budget, for a callee that
touches no memory.* For a dialect lawful in its monotonicity, whose values'
refinement is reflexive and transitive, at a layout and naming at which its
ops ignore the memories where they touch none: let $`M` be a valid module,
$`g` a function of $`M` whose parameter types have finitely many argument
vectors, $`b` a new body, and $`M'` the module with $`g`'s body replaced by
$`b`, in which $`g` reaches no memory. If $`g` in $`M'`
refines $`g` in $`M` from given memories, then every function of $`M` is
refined by its counterpart in $`M'`, from given memories and with memory,
calls and recursion included. If $`g` reaches no memory in $`M`
too, it is enough that $`g` in $`M'` refine $`g` in $`M` with
memory.

It is the
{ref "The-fir-specification--Memory--Replacing-a-callee___-with-memory"}[theorem on replacing a callee with memory],
whose budget comes from the finitely many argument vectors, as for runs in
the set monad. The human ruled on #373 on 2026-11-13 that congruence takes
this form for a callee that touches no memory, and asks for the budget only
of a callee that touches memory, until #214.
:::
