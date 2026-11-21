import VersoManual
import Fir.Execution.TraceSteps
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the first steps of a marked trace, which renders
`Fir.Execution.TraceSteps` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The first steps of a marked trace: readable blocks" =>

:::moduleDocs (fingerprint := "17589780618894415870")
:::

:::readable Fir.Step.ticks Fir.Step.ticks_append (fingerprint := "11321973910066212008")
*Definition: steps.* $`\mathrm{ticks}(m)` is the number of steps
$`\mathsf{tick}` of the marked trace $`m`.

*Theorem.* $`\mathrm{ticks}(m \mathbin{+\!\!+} m') = \mathrm{ticks}(m) + \mathrm{ticks}(m')`.
:::

:::readable Fir.Step.upTo_prefix Fir.Step.upTo_mono Fir.Step.upTo_upTo Fir.Step.upTo_of_prefix Fir.Step.upTo_of_ticks_le Fir.Step.upTo_append_of_lt Fir.Step.actsOf_prefix (fingerprint := "12826450847370718335")
*Theorems: first steps.* Write $`m{\restriction}N` for the first $`N`
steps of $`m`, everything before its step $`N + 1`, and $`m \preceq m'`
for "$`m` starts $`m'`".

* $`m{\restriction}N \preceq m`, and $`m{\restriction}N \preceq m{\restriction}N'`
  when $`N \le N'`;
* $`(m{\restriction}N'){\restriction}N = m{\restriction}N` when $`N \le N'`;
* $`m \preceq m'` implies $`m{\restriction}N \preceq m'{\restriction}N`;
* $`m{\restriction}N = m` when $`\mathrm{ticks}(m) \le N`;
* $`(m \mathbin{+\!\!+} r){\restriction}N = m{\restriction}N` when $`N < \mathrm{ticks}(m)`;
* $`m \preceq m'` implies that the acts of $`m` start the acts of $`m'`.
:::

:::readable Fir.Step.upTo_isRefinedBy (fingerprint := "16680992716034666090")
*Theorem.* Marked traces $`m \sqsubseteq m'`, a step by a step and an act
by an act that refines it, have $`m{\restriction}N \sqsubseteq m'{\restriction}N`.
:::

:::readable Fir.List.IsPrefix.antisymm Fir.List.IsPrefix.getElem?_some Fir.List.IsRefinedPrefix.of_prefix (fingerprint := "8817046527577682417")
*Theorems: lists.* Lists that start each other are equal. A list that
starts $`l'` has, at each of its places, the element of $`l'` there. A
list refined by a prefix of $`l'` is refined by a prefix of each list that
$`l'` starts.
:::

:::readable Fir.List.exists_often (fingerprint := "12245040938439311886")
*Theorem: the pigeonhole principle.* When, at infinitely many budgets $`n`
with $`P(n)`, the value $`g(n)` lies in the finite list $`L`, some member
$`a` of $`L` is $`g(n)` at infinitely many budgets $`n` with $`P(n)`.
:::
