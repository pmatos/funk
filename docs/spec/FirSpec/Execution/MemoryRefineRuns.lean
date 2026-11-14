import VersoManual
import Fir.Execution.MemoryRefineRuns
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on refined arguments and memories, which
renders `Fir.Execution.MemoryRefineRuns` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Refined arguments and memories: readable blocks" =>

:::moduleDocs (fingerprint := "5207053525379043121")
:::

:::readable Fir.Func.memOps_allowedBelow (pin := Fir.MemAllowedBelow) (pin := Fir.MemCallsRefined) (pin := Fir.MemCallsBounded) (pin := Fir.MemMonotoneOps) (pin := Fir.Func.MemOpsMonotone) (fingerprint := "6446781191699385464")
*Theorem: every path of the target with memory that runs out of fuel or
returns, allowed below a budget.* Let the target module $`M'` run each
call with memory as the source $`M` does, with its calls bounded by
$`\mathit{bound}`, and every op of $`M`'s functions,
of $`f` and of $`o^*` that runs by its own rule be monotone with memory.
Let $`E \sqsubseteq E'`, $`S \sqsubseteq S'`, and
$`(\mathit{bound} + 1)(N + 1) \le n`. Then each path of
$`\mathrm{ops}_{M'}(n, f, E', o^*) \mathbin{@} S'` that runs out of fuel or
returns is allowed below the ratio $`\mathit{bound} + 1` by
$`\mathrm{ops}_M(\cdot, f, E, o^*) \mathbin{@} S` at $`N`. The proof is by
strong induction on $`n`, from every memories, as for runs in the set
monad.
:::

:::readable Fir.Func.memRunsFrom_retUB_allowed (pin := Fir.MemCallsRefined) (pin := Fir.Func.MemOpsMonotone) (pin := Fir.Func.memRunsFrom) (pin := Fir.observable) (fingerprint := "11921490865856683547")
*Theorem: every return and UB of the target from given memories, allowed.*
Let the target module $`M'` run each call with memory as the source $`M`
does, and every op of $`M`'s functions and of $`f` that runs by its own
rule be monotone with memory. On arguments $`\vec{v} \sqsubseteq \vec{v}'`
and from memories $`S \sqsubseteq S'`, each return and each UB in the
behaviour of $`f` in $`M'` from $`S'` is allowed by an outcome of its
behaviour in $`M` from $`S`: UB, or a return of values and memories that
the target's refine. It is the theorem on returns and UB with memory, for
the entry block's ops in a frame. No black box needs a budget.
:::

:::readable Fir.Func.memRunsFrom_isRefinedBy_of_calls (pin := Fir.MemCallsRefined) (pin := Fir.MemCallsBounded) (pin := Fir.Func.MemOpsMonotone) (pin := Fir.Func.memRunsFrom) (pin := Fir.observable) (fingerprint := "17947935108510817891")
*Theorem: two modules with memory, compared call by call.* Let the target
module $`M'` run each call with memory as the source $`M` does, with its
calls bounded by $`\mathit{bound}`, and every
op of $`M`'s functions and of $`f` that runs by its own rule be monotone
with memory. On arguments $`\vec{v} \sqsubseteq \vec{v}'` and from memories
$`S \sqsubseteq S'`, the behaviour of $`f` in $`M'` from $`S'`, the
memories it ends with included, refines its behaviour in $`M` from $`S`:

$$`\mathrm{obs}(\mathrm{runs}^S_{M,f}(\vec{v}, S)) \sqsubseteq \mathrm{obs}(\mathrm{runs}^S_{M',f}(\vec{v}', S'))`

Each return or UB of the target is allowed by the source at some budget,
by the theorem above. When the target diverges and
the source hits no UB, for each budget $`N` of the source the target runs
out of fuel at $`(\mathit{bound} + 1)(N + 1)`, on a path that the source
allows below that ratio at $`N`: the source runs out of fuel there, so it
diverges.
:::

:::readable Fir.Func.memRunsFrom_args_isRefinedBy (fingerprint := "3135102364523871184")
*Theorem: refined arguments and memories.* In every module, when every op
of its functions and of $`f` that runs by its own rule is monotone with
memory, let $`\vec{v} \sqsubseteq \vec{v}'` and $`S \sqsubseteq S'`: a
poison replaced by any value, and a poison unit by any unit. Then the
behaviour of $`f` on $`\vec{v}'` from $`S'` refines its behaviour on
$`\vec{v}` from $`S`, values and memories, calls and recursion included.
It is the theorem above, with the module as its own target and no black
box, so no budget.
:::
