import VersoManual
import Fir.Execution.SummaryLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on joins and the walk, which renders
`Fir.Execution.SummaryLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Joins and the walk: readable blocks" =>

:::moduleDocs (fingerprint := "1767705841404451245")
:::

:::readable Fir.MemSet.Sub.refl Fir.Effects.le_refl Fir.Effects.le_trans Fir.Effects.empty_le Fir.Effects.le_all (fingerprint := "14338473674192180061")
*Theorems: below is a preorder with a least and a greatest set.* Every set
of memories and every effect set is below itself; if $`e \le e'` and
$`e' \le e''`, then $`e \le e''`; and
$`\emptyset \le e \le \top_{\mathit{eff}}` for every effect set $`e`.
:::

:::readable Fir.Effects.callerView_le Fir.Effects.callerView_mono Fir.Effects.le_callerView (fingerprint := "10931697573204581757")
*Theorems: what a caller sees.* $`\mathrm{caller}(e) \le e`; if
$`e \le e'`, then $`\mathrm{caller}(e) \le \mathrm{caller}(e')`; and a
set without $`\mathsf{control}` below $`e'` is below
$`\mathrm{caller}(e')`.
:::

:::readable Fir.MemSet.has_join Fir.Effects.le_join_left Fir.Effects.le_join_right Fir.Effects.join_le Fir.Effects.callerView_join_le (fingerprint := "1280021013683539252")
*Theorems: the join is the least set above both.* The join of two sets
of memories holds a memory exactly when either does. $`e \le e \sqcup e'`
and $`e' \le e \sqcup e'`; if $`e \le c` and $`e' \le c`, then
$`e \sqcup e' \le c`; and if $`\mathrm{caller}(e) \le c` and
$`\mathrm{caller}(e') \le c`, then $`\mathrm{caller}(e \sqcup e') \le c`.
:::

:::readable Fir.Effects.foldl_join Fir.Effects.le_joinAll Fir.Effects.joinAll_le (fingerprint := "15120802591703493829")
*Theorems: the join of a list.* A join from the left from $`i` is above
$`i` and above each set it joins, and below every set above them all. So
each $`e_j \le \bigsqcup_i e_i`, and if every $`e_i \le c`, then
$`\bigsqcup_i e_i \le c`.
:::

:::readable Fir.SymbolTable.mem_callees (fingerprint := "18192562178099201744")
*Theorem: the callees of a function.* $`c` is a callee of $`f` in $`t`
exactly when $`c` names a function of $`t` and some op of $`f`, at any
depth, calls $`c`.
:::

:::readable Fir.SymbolTable.mem_reach (fingerprint := "17889193172321837461")
*Theorem: the walk reaches its work.* Every symbol of $`S`, and every
symbol of $`W` that names a function of $`t`, is in
$`\mathrm{reach}_t(W, S)`.
:::

:::readable Fir.SymbolTable.reach_closed (fingerprint := "460886769540299218")
*Theorem: what the walk reaches is closed under calls.* If every callee
of the function of each symbol of $`S` is in $`S` or $`W`, then every
callee of the function of each symbol of $`\mathrm{reach}_t(W, S)` is in
it too. In particular, $`\mathrm{reach}_t([s], [])` holds every callee of
each function it holds.
:::

:::readable Fir.SymbolTable.reach_sub (fingerprint := "17206117230705811108")
*Theorem: the walk reaches nothing more.* If a set of symbols $`C` holds
$`S` and $`W`, and every callee of the function of each symbol of $`C`,
then $`C` holds $`\mathrm{reach}_t(W, S)`.
:::
