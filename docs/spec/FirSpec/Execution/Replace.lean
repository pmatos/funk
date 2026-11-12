import VersoManual
import Fir.Execution.Replace
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on replacing a callee, which renders
`Fir.Execution.Replace` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Replacing a callee: readable blocks" =>

:::moduleDocs (fingerprint := "13726337576915520375")
:::

:::readable Fir.Func.replaceBody Fir.Item.replaceBody Fir.Module.replaceBody (fingerprint := "10617108302315699159")
*Definition: replacing the body of the function with a symbol.* For a
symbol $`s` and a region $`b`, $`f[s \leftarrow b]` is the function $`f`
with the body $`b` when the symbol of $`f` is $`s`, and $`f` unchanged
otherwise. An item that is a function $`f` becomes $`f[s \leftarrow b]`,
and a nested module is unchanged, since its functions are in its own
symbol table. An item of a dialect's kind is unchanged too. For a
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[module]
$`M`, $`M[s \leftarrow b]` replaces each item of $`M` so, in the same
order, and keeps the dialect set, the data layout and the location table.

Every function keeps its symbol, its parameters and its result types, and
every other function keeps its body. A caller reaches a callee only by
its symbol (ADR-2026-10-29-2012), so this replaces the callee $`s` for
every caller at once: it is what an optimizer does when it rewrites one
function of a module.
:::

:::readable Fir.Module.funcs_replaceBody Fir.Func.replaceBody_of_ne Fir.Func.replaceBody_of_eq Fir.Module.func?_replaceBody (pin := Fir.Module.func?) (fingerprint := "380502133935660617")
*Theorems: what a replacement changes.* For every module $`M`, symbol
$`s`, region $`b` and function $`f`:

* the functions of $`M[s \leftarrow b]` are those of $`M`, each $`f` as
  $`f[s \leftarrow b]`;
* when the symbol of $`f` is not $`s`, $`f[s \leftarrow b] = f`;
* when it is $`s`, $`f[s \leftarrow b]` is $`f` with the body $`b`;
* for every symbol $`x`, $`\mathrm{lookup}_{M[s \leftarrow b]}(x)` is
  $`\mathrm{lookup}_M(x)` with its body replaced when its symbol is $`s`,
  and undefined exactly when $`\mathrm{lookup}_M(x)` is undefined.

Here $`\mathrm{lookup}_M(x)` is the first function of $`M` whose symbol is
$`x`, the one that a
{ref "The-fir-specification--Execution--The-interpreter"}[call]
of $`x` runs. So a call of any other symbol runs the same function in the
new module as in the old.
:::

:::readable Fir.Module.func?_of_mem (pin := Fir.Module.func?) (fingerprint := "8088830654535726145")
*Theorem: in a module whose symbols are unique, a call of a function's
symbol runs it.* If no two functions of $`M` have the same symbol, then
for every function $`g` of $`M` with the symbol $`s`,
$`\mathrm{lookup}_M(s) = g`. A
{ref "The-fir-specification--Validation--The-general-rules"}[valid module]
has unique symbols, so its calls of $`s` are calls of $`g`.
:::

:::readable Fir.Module.symbols_replaceBody Fir.Module.context_replaceBody Fir.Module.dialectItems_replaceBody (pin := Fir.Module.symbols) (pin := Fir.Module.context) (fingerprint := "5476321169022967364")
*Theorems: a replacement keeps the symbol table and the context of
validation.* For every module $`M`, symbol $`s` and region $`b`, the
{ref "The-fir-specification--Validation--Scope-and-symbols"}[symbol table]
of $`M[s \leftarrow b]` is that of $`M`, since every function keeps its
symbol and its type; so is the context in which validation checks its
functions, which is the symbol table and the keys of the location table.
The items of a dialect's kind of its own table are those of $`M`.
:::

:::readable Fir.Item.name_replaceBody Fir.Item.tablesIn_replaceBody (fingerprint := "3259367735023084775")
*Theorems: replacing a body keeps the symbols and the nested tables.* For
every symbol $`s`, region $`b` and item $`i`, the item with the body
replaced has the symbol of $`i`. For every list of items, the items with
the body replaced hold the same
{ref "The-fir-specification--Validation--Scope-and-symbols"}[symbol tables]:
a function holds none, and a nested module is unchanged.
:::

:::readable Fir.Module.valid_replaceBody (pin := Fir.Module.Valid) (fingerprint := "17437293996579678251")
*Theorem: a valid module stays valid when the new function is valid.* For
every dialect with its validation rules, let $`M` be a
{ref "The-fir-specification--Validation--The-general-rules"}[valid module],
$`s` a symbol and $`b` a region, and let each function $`g` of $`M` with
the symbol $`s`, given the body $`b`, be valid in the context of $`M`, with
each of its types naming a memory that the layout of $`M` declares. Then
$`M[s \leftarrow b]` is valid: the symbols of its own table are those of
$`M`, so still unique; its location table, its dialect set and its layout
are those of $`M`; each of its functions is valid in its context, which is
that of $`M`, and its types name memories of the layout; and its nested
modules, and so the tables they hold, are those of $`M`.

So the new body needs to be checked alone, against the old module's
symbol table; every other function was already valid there.
:::

:::readable Fir.Func.runs_exhausted_down (fingerprint := "8224768621522136213")
*Theorem: a function that runs out of fuel runs out of fuel with fewer
steps.* For every function $`f`, run in a module $`M`, argument vector $`a`
and budgets $`n \leq m`: if the
{ref "The-fir-specification--Execution--The-runs-of-a-function___-and-fuel-monotonicity"}[runs]
of $`f` on $`a` run out of fuel at $`m`, they run out of fuel at $`n`.
It is the theorem of the section on
{ref "The-fir-specification--Execution--The-ways-a-step-goes-on"}[the ways a step goes on]
for a whole function. So on each argument vector, a function runs out of
fuel at every budget, or from some budget on never does.
:::

:::readable Fir.exists_common_bound (fingerprint := "4821431095657372811")
*Theorem: one bound serves finitely many argument vectors.* Let the list
$`L` hold every element of a set $`A`, and let $`Q(a, m)` be a property of
an element $`a \in A` and a number $`m` that passes to smaller numbers:
$`m \leq m'` and $`Q(a, m')` give $`Q(a, m)`. Then there is a $`\beta` such
that for every $`a \in A`, either $`Q(a, m)` holds for every $`m`, or it
holds for no $`m \geq \beta`.

With $`Q(a, m)` "the new callee runs out of fuel at $`m` on $`a`", this
gives the black box its bound when the callee's parameter types have
finitely many argument vectors (`docs/decisions/semantics-refinement.md#congruence-in-the-callee`). Without that, one
bound may not serve them all: a caller whose arguments grow without limit
can make the new callee run longer and longer before it returns.
:::

:::readable Fir.Func.runs_replaceBody_isRefinedBy (pin := Fir.FuncRuns.IsRefinedBy) (pin := Fir.Func.OpsMonotone) (pin := Fir.BlackBox) (fingerprint := "17377090128024739525")
*Theorem: congruence in the callee.* In every dialect, let $`M` be a
module, and suppose that:

* every function of $`M` has
  {ref "The-fir-specification--Execution--Returns-and-UB___-followed-back"}[monotone ops];
* the refinement of values is reflexive, $`v \sqsubseteq_t v`, and
  transitive, $`u \sqsubseteq_t v` and $`v \sqsubseteq_t w` giving
  $`u \sqsubseteq_t w`, for every type $`t`;
* no two functions of $`M` have the same symbol;
* $`g` is a function of $`M` with the symbol $`s`, $`b` a region, and the
  parameter types of $`g` have finitely many argument vectors;
* with $`M' = M[s \leftarrow b]` and $`g' = g[s \leftarrow b]`, the runs
  of $`g'` in $`M'`
  {ref "The-fir-specification--Execution--Refinement"}[refine]
  the runs of $`g` in $`M`: on every argument vector $`a`, the observable
  behaviour of $`g'` in $`M'` refines that of $`g` in $`M`.

Then for every function $`f` of $`M`, the runs of $`f[s \leftarrow b]` in
$`M'` refine the runs of $`f` in $`M`: $`f` itself, or $`g'` when $`f`
is $`g`. Calls and recursion are included (`docs/decisions/semantics-refinement.md#congruence-in-the-callee`).

This is what makes a compiler's pass over one function sound for the
whole program: replace a callee by a body that, run in the new module,
refines it, and every caller is refined.

The hypothesis compares $`g'` in the new module with $`g` in the old. A
callee that calls back, itself or its callers, calls the new body in
$`M'`, so only its runs in $`M'` say what a call of it does there. A
weaker hypothesis, that $`g'` run in the old module refines $`g`, would
make the theorem false: if $`g` returns $`0`, the body that calls $`s`
and returns its result refines it in $`M`, where it calls the old body;
in $`M'` it calls itself, and never returns.

The proof makes every call of $`s` a
{ref "The-fir-specification--Execution--Calls-as-black-boxes"}[black box]
from $`g` in $`M` to $`g'` in $`M'`, and every other symbol names the
same function in both. The black box refines: on refined arguments,
$`g` is refined by itself, by
{ref "The-fir-specification--Execution--Refined-arguments"}[refined arguments],
and that by $`g'`, by the hypothesis, and refinement is transitive. Its
bound is the one bound for the finitely many argument vectors, above. The
section on refined arguments then gives the theorem for each $`f` other
than $`g`. Monotonicity is asked only of the old module's functions: a
call of $`s` is a black box, whose new body the proof does not run.
:::
