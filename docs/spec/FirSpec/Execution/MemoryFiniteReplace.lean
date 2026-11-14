import VersoManual
import Fir.Execution.MemoryFiniteReplace
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on congruence in the callee with ops of
finitely many outcomes, which renders `Fir.Execution.MemoryFiniteReplace`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Congruence in the callee with ops of finitely many outcomes: readable blocks" =>

:::moduleDocs (fingerprint := "3466237653735662060")
:::

:::readable Fir.Func.memRunsFrom_isRefinedBy_of_opsFinite (pin := Fir.OpsFinite) (pin := Fir.MemCallsRefined) (pin := Fir.Func.MemOpsMonotone) (pin := Fir.Func.memRunsFrom) (pin := Fir.observable) (fingerprint := "5738740363365443155")
*Theorem: two modules with memory, compared call by call, with no budget.*
Let the target module $`M'` run each call with memory as the source $`M`
does, the ops of the dialect have finitely many outcomes, and every op of
$`M`'s functions and of $`f` that runs by its own rule be monotone with
memory. On arguments $`\vec{v} \sqsubseteq \vec{v}'` and from memories
$`S \sqsubseteq S'`, the behaviour of $`f` in $`M'` from $`S'`, the
memories it ends with included, refines its behaviour in $`M` from $`S`:

$$`\mathrm{obs}(\mathrm{runs}^S_{M,f}(\vec{v}, S)) \sqsubseteq \mathrm{obs}(\mathrm{runs}^S_{M',f}(\vec{v}', S'))`

Each return or UB of the target is allowed by the source, as in
{ref "The-fir-specification--Memory--Refined-arguments-and-memories"}[refined arguments and memories].
When the target diverges and the source hits no UB, the source runs out of
fuel at every budget $`N`: if it did not at $`N`, some budget of the target
would not either, by
{ref "The-fir-specification--Memory--Divergence-with-ops-of-finitely-many-outcomes"}[divergence with ops of finitely many outcomes].
:::

:::readable Fir.Func.memRunsFrom_replaceBody_isRefinedBy_of_opsFinite (pin := Fir.FuncRuns.IsRefinedBy) (pin := Fir.OpsFinite) (pin := Fir.Func.MemOpsMonotone) (fingerprint := "5056365940688537200")
*Theorem: congruence in the callee, with memory, with no budget.* In a
module $`M` whose symbols are unique, let every op of its functions that
runs by its own rule be monotone with memory, the ops of the dialect have
finitely many outcomes, and the refinement of values be reflexive and
transitive. Let $`g` be a function of $`M`, and $`g'` and $`M'` be $`g`
and $`M` with the body of $`g` replaced. If $`g'` in $`M'` refines $`g`
in $`M` from given memories, values and memories, then every function of
$`M` is refined so by its counterpart in $`M'`:

$$`\mathrm{runs}^S_{M,g} \sqsubseteq \mathrm{runs}^S_{M',g'} \implies \forall f \in M.\ \mathrm{runs}^S_{M,f} \sqsubseteq \mathrm{runs}^S_{M',f'}`

Unlike
{ref "The-fir-specification--Memory--Replacing-a-callee___-with-memory"}[replacing a callee with memory],
it asks for no budget for $`g'`, whatever its parameter types and whatever
it does to the memories. This is the form that König's lemma over the
tree of choices gives (`docs/decisions/semantics-refinement.md#congruence-in-the-callee`).
:::

:::readable Fir.Func.memRuns_replaceBody_isRefinedBy_of_opsFinite (pin := Fir.LawfulDialectMonotone) (fingerprint := "2517903228036907197")
*Theorem: congruence in the callee, with memory, with no budget, for a
lawful dialect.* For a dialect lawful in its monotonicity, in a valid
module, at a layout and naming of the dialect's memories at which its ops
have finitely many outcomes, whose values' refinement is reflexive and
transitive: if $`g'` refines $`g` from given memories, replacing the body
of $`g` refines every function of the module from given memories, and so
with memory, calls and recursion included, whatever the new body.
:::
