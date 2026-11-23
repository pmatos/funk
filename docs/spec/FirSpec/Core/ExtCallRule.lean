import VersoManual
import Fir.Core.ExtCallRule
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core's traced external-call
rule, which renders `Fir.Core.ExtCallRule` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "The core's traced external-call rule: readable blocks" =>

:::moduleDocs (fingerprint := "7479641758852283463")
:::

:::readable Fir.Core.Ty.poison Fir.Core.readReply Fir.Core.TraceM.reply (fingerprint := "1492601151479986347")
*Definition: reading back the world's reply.* $`\mathsf{poison}_t` is the
poison of the core type $`t`. In the traced state $`s`, the world's reply
$`\vec{v}` reads back, for results of the types $`r_1, \dots, r_k`, as
$`\vec{v}` with each pointer read back by its handle
($`\mathrm{back}_s`), when the values of $`\vec{v}` have the types
$`r_1, \dots, r_k` and each pointer reads back; otherwise the world cannot
give it, and the call has no outcome for it.
:::

:::readable Fir.Core.traceExtCall Fir.Core.traceExtCall_iff (fingerprint := "6205761472924571035")
*Definition: the core's traced external-call rule.* A call of the
declaration $`g` on the arguments $`\vec{w}`, holding the pointers
$`\vec{q}`, for results of the types $`\vec{r}`, from the traced state
$`s`: let $`s_1 = \mathrm{escapeCall}_s(\vec{q})`. The call shows the act
$`\langle \mathrm{ofCall}_{s_1}(g, \vec{w}), (\vec{v}, \vec{c}) \rangle`
for each reply $`\vec{v}` and actions $`\vec{c}` of the world that it can
take from $`s_1`, leaving $`s'`, and gives $`\vec{v}` read back in $`s'`
as its results, in $`s'`.
:::

:::readable Fir.Core.ptrs_poisons Fir.Core.traceExtCall_exists Fir.Core.traceExtCall_types (fingerprint := "4675878395504983201")
*Theorems: an outcome, of the call's types.* A poison of each type holds
no pointer, so from every traced state the world can answer with a poison
of each result type and no action: the rule has an outcome. Its results
have the call's result types, in order.
:::

:::readable Fir.Core.traceExtCall_finite (fingerprint := "12836000717006805802")
*Theorem: finitely many outcomes, given the world's answers.* The world's
answer to the call's one event fixes its reply and actions, so the
outcome: the rule has finitely many outcomes, given the world's answers.
:::

:::readable Fir.Core.traceExtCall_isRefinedBy (fingerprint := "14689215148710973932")
*Theorem: monotone when the same allocations escape, in the same order.*
On arguments $`\vec{w} \sqsubseteq \vec{w}'`, from traced states
$`s \sqsubseteq s'`, when

$$`\mathrm{escapeCall}_s(\vec{q}).\mathrm{escaped} = \mathrm{escapeCall}_{s'}(\vec{q}').\mathrm{escaped}`

each way the call on $`\vec{w}'` from $`s'` may end is allowed by a way
the call on $`\vec{w}` from $`s` may end, with the same reply, actions
and results, an event that the other's refines, and a traced state that
the other's refines. The two lists must be equal, the same allocations in
the same order (Q6). Without it the rule is not monotone: where the source
has poison and the target a pointer, the target lets escape an allocation
the source does not (Q4).
:::
