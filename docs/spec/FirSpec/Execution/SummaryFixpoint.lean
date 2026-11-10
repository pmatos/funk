import VersoManual
import Fir.Execution.SummaryFixpoint
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the least fixpoint of the calls,
which renders `Fir.Execution.SummaryFixpoint` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "The summary is the least fixpoint: readable blocks" =>

:::moduleDocs (fingerprint := "232759440770060555")
:::

:::readable Fir.SymbolTable.Closed (fingerprint := "3623272267800276189")
*Definition: an assignment closed under calls.* An assignment $`T` of an
effect set to each symbol is _closed_ under the calls of a table $`t`
when, for each symbol $`s` that names a function $`f` of $`t` and each op
$`o` of $`f` at any depth:

* $`\mathrm{own}_t(o) \le T(s)`;
* if $`o` calls a function $`c` of $`t`, then $`T(c) \le T(s)`.

The summary of each function is a solution of these inequalities, and the
least one.
:::

:::readable Fir.SymbolTable.funcOwn_le Fir.SymbolTable.summary_le (fingerprint := "790633999358419533")
*Theorems: the summary is below every closed assignment.* If $`T` is
closed, then $`\mathrm{own}_t(f) \le T(s)` for the function $`f` that
$`s` names, and $`\mathrm{sum}_t(s) \le T(s)` for every symbol $`s`:
every function that $`s` reaches has its set below $`T(s)`, since the
symbols whose set is below $`T(s)` are closed under calls.
:::

:::readable Fir.SymbolTable.funcOwn_le_summary Fir.SymbolTable.summary_le_of_callee Fir.SymbolTable.summary_closed (fingerprint := "675438268539080094")
*Theorems: the summary is closed.* What a caller sees of a function's own
ops is below its summary, since a function reaches itself. The summary of
a callee of $`f` is below the summary of $`f`: what the callee reaches,
$`f` reaches. So $`\mathrm{sum}_t` is closed under the calls of $`t`, and
with the theorem above it is the least closed assignment: the least
fixpoint of the calls, recursion included.
:::

:::readable Fir.SymbolTable.opOwn_le Fir.SymbolTable.summary_control (fingerprint := "11120820603872178761")
*Theorems: a summary has no control.* What a caller sees of an op is
below $`\mathrm{caller}(\top_{\mathit{eff}})`, and so is every summary:
$`\mathsf{control} \notin \mathrm{sum}_t(s)`. A call is not a
terminator, whatever its callee's ops are.
:::

:::readable Fir.SymbolTable.effects_le_summary Fir.SymbolTable.opEffects_le_summary (fingerprint := "2051318579800569848")
*Theorems: a call carries its callee's effects.* For each op $`o` of the
function that $`s` names, at any depth,
$`\mathrm{caller}(\mathrm{eff}(o)) \le \mathrm{sum}_t(s)` and
$`\mathrm{caller}(\mathrm{eff}_t(o)) \le \mathrm{sum}_t(s)`: the effects
of an op in place, its callee's summary included, are below its
function's summary, but for control.
:::
