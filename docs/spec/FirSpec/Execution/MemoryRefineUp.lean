import VersoManual
import Fir.Execution.MemoryRefineUp
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on returns and UB with memory, followed
back, which renders `Fir.Execution.MemoryRefineUp` (ADR-2026-11-05-2012).
Each block explains declarations of that module and pins their fingerprint;
the build fails when the Lean changes under it.
-/

#doc (Manual) "Returns and UB with memory, followed back: readable blocks" =>

:::moduleDocs (fingerprint := "10832409791610803295")
:::

:::readable Fir.MemMonotoneOps Fir.Func.MemOpsMonotone Fir.Func.MemOpsMonotone.enter Fir.Func.MemOpsMonotone.jump (pin := Fir.OpMemMonotone) (fingerprint := "17780227716261539167")
*Definitions and theorems: ops monotone with memory.* A list of ops is
monotone with memory when each of its ops that is a terminator or calls no
function is
{ref "The-fir-specification--Memory--Monotonicity-with-memory"}[monotone]
in the semantics in the state layer; a function is when the ops of each of
its blocks are. A run of such a function starts at the ops of one of its
blocks, and a jump goes to the ops of one of its blocks, so they are
monotone with memory too.
:::

:::readable Fir.MemCallsRefined.callee_allowed (pin := Fir.MemCallsRefined) (fingerprint := "2921739894448207099")
*Theorem: a callee's return or UB, allowed.* In modules whose calls
refine, a return or UB of a call's callee in the target, in its frame,
entered on arguments and from memories that refine the source's, is
allowed by the source's callee in its frame: the same function, by the
induction, which covers its ops from $`\mathrm{enter}(S) \sqsubseteq \mathrm{enter}(S')`,
or a black box.
:::

:::readable Fir.Func.memOps_allowed (pin := Fir.MemAllowed) (pin := Fir.MemCallsRefined) (pin := Fir.MemMonotoneOps) (pin := Fir.Func.MemOpsMonotone) (fingerprint := "13806622018855904798")
*Theorem: every return and UB of the target with memory, allowed.* Let
the target module $`M'` run each call with memory as the source $`M`
does, and every op of $`M`'s functions, of $`f` and of $`o^*` that runs by
its own rule be monotone with memory. Let $`E \sqsubseteq E'` and
$`S \sqsubseteq S'`. Then each return and each UB of
$`\mathrm{ops}_{M'}(n, f, E', o^*) \mathbin{@} S'` is allowed by
$`N \mapsto \mathrm{ops}_M(N, f, E, o^*) \mathbin{@} S`: UB at some budget, or
a return at some budget of values and memories that the target's refine.

The proof is the one for runs in the set monad, by strong induction on
$`n`, for every function and from every memories. Each op runs alike in
both, on operands and from memories of which the target's refine the
source's, so what it does in the target is allowed by what it does in the
source, with memories that refine the source's after it. No black box
needs a budget here: a path that runs out of fuel asks nothing.
:::
