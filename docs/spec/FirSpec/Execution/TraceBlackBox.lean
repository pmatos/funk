import VersoManual
import Fir.Execution.TraceBlackBox
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on two modules in the traced layer,
compared call by call, which renders `Fir.Execution.TraceBlackBox`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Two modules in the traced layer, compared call by call: readable blocks" =>

:::moduleDocs (fingerprint := "1650275520245198217")
:::

:::readable Fir.TraceEnd.withState Fir.Step.actsOf_append (fingerprint := "9274160893709162379")
*Definition: the end state of a return.* A path of a run ends, with the
traced state of each return: $`\mathsf{ret}~\vec{w}` in the traced state
$`s` becomes $`\mathsf{ret}~(\vec{w}, s)`.

*Theorem.* The acts of $`m \mathbin{+\!\!+} m'` are those of $`m`, then
those of $`m'`.
:::

:::readable Fir.Func.traceFrom Fir.Func.traceFrom_ret_iff Fir.Func.traceFrom_ub_iff Fir.Func.traceFrom_exhausted_iff (fingerprint := "16158629417972949940")
*Definition: traced runs from a given traced state.* The traced runs of
$`f` in $`M` from given traced states run $`f` on each argument vector from
each traced state $`s`, in a traced layer of marked traces, at each budget,
and return its values with the traced state each return ends in.

*Theorems.* A return of $`(\vec{w}, s_1)` after $`m`, UB after $`m`, and
running out of fuel after $`m`, of those runs from $`s`, are, and come
from, the same ways of ending of $`f`'s entry block's ops in its frame from
$`s`.
:::

:::readable Fir.TSomeUB Fir.TAllowed Fir.TAllowed.of_someUB Fir.TAllowed.of_step (pin := Fir.TraceEnd.trace) (fingerprint := "922765940895484054")
*Definition: allowed at some budget.* A source, a run $`\mathit{src}_N` at
each budget $`N`, allows a path of the target that hits UB or returns when
it hits UB at some budget after acts that the target's path first shows,
refined; or, for a return of $`v'` after $`m'` in $`s'`, it returns at some
budget some $`v \sqsubseteq v'` after $`m` in $`s`, with
$`\mathrm{acts}(m) \sqsubseteq \mathrm{acts}(m')` and $`s \sqsubseteq s'`.
The steps of the two marked traces are not compared. Running out of fuel
and being stuck ask nothing here.

*Theorems.* UB at some budget after acts that a path first shows allows it.
A path that the rest of a run allows is allowed by the whole after acts
that refine the target's first ones, when each way the rest ends at $`N`,
done, is a way the whole ends at $`N_0 + N + 1` after the marked trace
$`t`, with $`k` more steps left on a return.
:::

:::readable Fir.Func.traceCall_tAllowed (fingerprint := "7430243069012207286")
*Theorem: leaving a frame keeps what is allowed.* When each path of the
target callee's ops, from $`s'` with a frame entered, is allowed by the
source's, from $`s` with a frame entered, each path of the target callee in
its frame from $`s'` is allowed by the source's in its frame from $`s`:
leaving a frame keeps refinement of traced states.
:::

:::readable Fir.TraceBlackBox Fir.TraceCallsRefined (fingerprint := "5449653143493034849")
*Definitions: traced black boxes, and modules whose calls refine in the
traced layer.* A _traced black box_ is a function $`g` of the source module
$`M` and a function $`g'` of the target module $`M'` with the same
parameter types, such that, on arguments $`\vec{v} \sqsubseteq \vec{v}'`
and from traced states $`s \sqsubseteq s'`,

$$`\mathrm{traceObservable}(g_M(\vec{v}, s)) \sqsubseteq \mathrm{traceObservable}(g'_{M'}(\vec{v}', s'))`

over their traced runs from given traced states, the traced states they end
in included. The target module _runs each call in the traced layer as the
source does_ when each symbol names the same function in both, or a traced
black box, and the source declares each symbol that the target declares,
for the same types.
:::

:::readable Fir.TraceCallsRefined.ext (pin := Fir.Module.func?_none_of_calls) (fingerprint := "5173545975530898859")
*Theorem: a call to a declaration in the target is one in the source, in
the traced layer.* When $`M'` runs each call in the traced layer as $`M`
does, a symbol that names no function of $`M'` and that $`M'` declares for
the types of a call names no function of $`M`, and $`M` declares it for
those types too: both run it by the same external-call rule.
:::

:::readable Fir.TraceBlackBox.sig Fir.TraceBlackBox.allowed (fingerprint := "4282305102550625657")
*Theorems: a black-box call, allowed.* A call that enters a black box's
target passes arguments of the parameter types of its source. A return or
UB of the target in its frame, called on arguments and from a traced state
that refine the source's, is allowed by the source's callee in its frame,
which starts: the black box's refinement gives UB of the source after acts
that the target first shows, refined, or a return after acts that the
target's refine, of values and a traced state that the target's refine.
:::
