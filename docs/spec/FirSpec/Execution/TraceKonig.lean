import VersoManual
import Fir.Execution.TraceKonig
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on divergence of a traced run, by König's lemma, which renders
`Fir.Execution.TraceKonig` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Divergence of a traced run, by König's lemma: readable blocks" =>

:::moduleDocs (fingerprint := "11926795971279751067")
:::

:::readable Fir.TRun.Truncates Fir.TRun.FinitelyMany Fir.TRun.ExhaustedAllowed (fingerprint := "10165934631249344372")
*Definition: what the source's run must do.* The run $`R` _truncates_
with $`W > 0` when each path that runs out of fuel at a budget $`n'` with
the marked trace $`m'` is cut, at each $`n \le n'`, to a path that runs out
of fuel at $`n` with a marked trace $`m \preceq m'`, with
$`\mathrm{ticks}(m) \le n`, and with $`m{\restriction}N = m'{\restriction}N`
whenever $`W (N + 1) \le n`.

$`R` has _finitely many traces_ when, at each budget and for each answer
stream, the marked traces of its paths that run out of fuel, whose acts
agree with the stream, lie in one finite list.

$`R` _allows_ $`R'` at each budget when each path of $`R'` that runs out
of fuel with $`m'` is allowed by a path of $`R` at the same budget that
runs out of fuel with $`m \sqsubseteq m'`, or hits UB with a refined prefix
of $`m'`.
:::

:::readable Fir.TRun.ub_or_paths Fir.TRun.ub_allows Fir.Step.actsOf_length_eq Fir.TRun.firstSteps_finite (fingerprint := "257247461392450263")
*Theorems.* When $`R` allows $`R'`, and $`R'` has at each budget a path
that runs out of fuel with a property $`Q`, either $`R` hits UB at some
budget after a refined prefix of such a path, or at every budget both have
paths that run out of fuel, the target's with $`Q`, refining the
source's. UB after a refined prefix of a target's path allows every
outcome that shows that path's acts at their places. Marked traces that
refine each other show as many acts. When $`R` truncates and has finitely
many traces, the first $`N` steps of its paths at every budget from $`C`
on, whose acts agree with one stream, lie in one finite list when
$`W (N + 1) \le C`: each is the first $`N` steps of the path cut at $`C`.
:::

:::readable Fir.TRun.diverge_allowed (fingerprint := "6952205701170830850")
*Theorem: silent divergence.* Let $`R` truncate, have finitely many
traces, and allow $`R'` at each budget. When $`R'` diverges silently after
$`t`, $`R` hits UB after a refined prefix of $`t`, or diverges silently
after some $`t_0 \sqsubseteq t`. From some budget on, the target shows all
of $`t` in its first $`N` steps. At the budget $`C = W (N + 1) + N`, the
source's paths, cut there, lie in a finite list, so by the pigeonhole
principle one value of their first $`N` steps occurs at infinitely many
budgets; its acts are $`t_0`. Cutting a path at a larger such budget
serves every budget.
:::

:::readable Fir.kmax Fir.le_kmax Fir.kmax_mono (fingerprint := "15133766703469888420")
*Definition.* $`\mathrm{kmax}_K(k)` is the largest of
$`K(0), \ldots, K(k)`. It is at least each of them and grows with $`k`.
:::

:::readable Fir.TRun.reacts_allowed (fingerprint := "15146803279197325906")
*Theorem: acts forever.* Let $`R` truncate, have finitely many traces,
and allow $`R'` at each budget. When $`R'` shows the infinite trace $`T`,
$`R` hits UB after a refined prefix of $`T`, or shows an infinite trace
$`T_0` with $`T_0(i) \sqsubseteq T(i)` at each $`i`. The first
$`K'(k) = \mathrm{kmax}_K(k) + k` steps of the source's paths form a tree
with finitely many nodes at each level. By König's lemma it has a branch of
nodes, each reached at infinitely many budgets, whose acts are $`T_0`.
Cutting longer paths along the branch serves every budget, the level
$`k` from the budget $`W (K'(k) + 1)` on.
:::
