import VersoManual
import Fir.Execution.MemoryReplace
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on replacing a callee, with memory,
which renders `Fir.Execution.MemoryReplace` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "Replacing a callee, with memory: readable blocks" =>

:::moduleDocs (fingerprint := "7640157692671390853")
:::

:::readable Fir.Func.memRunsFrom_replaceBody_isRefinedBy (pin := Fir.FuncRuns.IsRefinedBy) (pin := Fir.FuncRuns.BoundedBy) (pin := Fir.Func.MemOpsMonotone) (pin := Fir.MemBlackBox) (fingerprint := "17748345473618143949")
*Theorem: congruence in the callee, with memory.* In a module $`M` whose
symbols are unique, let every op of its functions that runs by its own rule
be monotone with memory, and the refinement of values be reflexive and
transitive. Let $`g` be a function of $`M`, and $`g'` and $`M'` be $`g`
and $`M` with the body of $`g` replaced
({ref "The-fir-specification--Execution--Replacing-a-callee"}[replacing a callee]).
If, on each argument vector and from each memories, the behaviour of $`g'`
in $`M'` refines that of $`g` in $`M`, values and memories, and the runs
of $`g'` from given memories are bounded by one budget $`B`, so that past
it no run of $`g'` from any memories runs out of fuel unless it diverges,
then every function of $`M` is refined so by its
counterpart in $`M'`:

$$`\mathrm{runs}^S_{M,g} \sqsubseteq \mathrm{runs}^S_{M',g'} \implies \forall f \in M.\ \mathrm{runs}^S_{M,f} \sqsubseteq \mathrm{runs}^S_{M',f'}`

Each call of $`g` is a black box with memory, whose refinement is refined
arguments and memories for $`g` in $`M`, then the hypothesis. Runs in the
set monad get $`B` from finitely many argument vectors; the memories a call
starts from are infinitely many, so here $`B` is a hypothesis, which #214
removes (`docs/decisions/semantics-refinement.md#refinement-with-memory`).
:::

:::readable Fir.Func.Valid.memOpsMonotone (fingerprint := "7140365292879792528")
*Theorem: a valid function's ops are monotone with memory.* When every
valid op instance that is a terminator or calls no function is monotone
in a semantics in the state layer, so is every such op of a valid function,
since each of its ops is a valid op instance.
:::

:::readable Fir.Func.memRunsFrom_args_isRefinedBy_of_lawful Fir.Func.memRuns_args_isRefinedBy_of_lawful (pin := Fir.LawfulDialectMonotone) (fingerprint := "7952930474160627859")
*Theorems: refined arguments, with memory, by the class alone.* For a
dialect lawful in its monotonicity, in a module whose functions are all
valid, at every naming of the dialect's memories: the behaviour of a
function on arguments $`\vec{v}'` from memories $`S'` refines its
behaviour on $`\vec{v} \sqsubseteq \vec{v}'` from $`S \sqsubseteq S'`,
values and memories; and its behaviour with memory on $`\vec{v}'` refines
its behaviour with memory on $`\vec{v}`, calls and recursion included,
whatever its ops do to the memories.
:::

:::readable Fir.Func.memRuns_replaceBody_isRefinedBy_of_bound (fingerprint := "7174405000707121818")
*Theorem: congruence in the callee, with memory, for a lawful dialect.*
For a dialect lawful in its monotonicity, in a valid module, at every
naming of the dialect's memories, the class gives that every op is
monotone with memory. The rest is asked as above: that refinement of
values be reflexive and transitive, that $`g'` refine $`g` from given
memories, and that its runs from given memories be bounded by one budget.
Then replacing the body of $`g` refines every function of the module from
given memories, and so with memory, calls and recursion included, whatever
the new body.
:::
