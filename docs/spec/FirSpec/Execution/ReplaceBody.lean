import VersoManual
import Fir.Execution.ReplaceBody
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on replacing a body, which renders
`Fir.Execution.ReplaceBody` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Replacing a body: readable blocks" =>

:::moduleDocs (fingerprint := "4593921381656862635")
:::

:::readable Fir.Func.replaceBody Fir.Item.replaceBody Fir.Module.replaceBody (fingerprint := "16462803487075343210")
*Definition: replacing the body of the function with a symbol.* For a
symbol $`s` and a region $`b`, $`f[s \leftarrow b]` is the function $`f`
with the body $`b` when the symbol of $`f` is $`s`, and $`f` unchanged
otherwise. An item that is a function $`f` becomes $`f[s \leftarrow b]`,
and a nested module is unchanged, since its functions are in its own
symbol table. An item of a dialect's kind, an aggregate's layout, a global
and an external declaration are unchanged too. For a
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[module]
$`M`, $`M[s \leftarrow b]` replaces each item of $`M` so, in the same
order, and keeps the dialect set, the data layout and the location table.

Every function keeps its symbol, its parameters and its result types, and
every other function keeps its body. A caller reaches a callee only by
its symbol (ADR-2026-10-29-2012), so this replaces the callee $`s` for
every caller at once: it is what an optimizer does when it rewrites one
function of a module.
:::

:::readable Fir.Module.funcs_replaceBody Fir.Func.replaceBody_of_ne Fir.Func.replaceBody_of_eq Fir.Module.func?_replaceBody (pin := Fir.Module.func?) (fingerprint := "4874706653414586257")
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

:::readable Fir.Module.func?_of_mem Fir.Module.func?_replaceBody_self Fir.Module.func?_replaceBody_of_ne (pin := Fir.Module.func?) (fingerprint := "17541982880925199527")
*Theorems: in a module whose symbols are unique, a call of a function's
symbol runs it.* If no two functions of $`M` have the same symbol, then
for every function $`g` of $`M` with the symbol $`s`,
$`\mathrm{lookup}_M(s) = g`. A
{ref "The-fir-specification--Validation--The-general-rules"}[valid module]
has unique symbols, so its calls of $`s` are calls of $`g`. In the module
with $`g`'s body replaced by $`b`, $`s` finds $`g` with the body $`b`, and
every other symbol finds what it finds in $`M`.
:::

:::readable Fir.Module.declares_replaceBody (pin := Fir.Module.declares) (fingerprint := "15349400318050950852")
*Theorem: replacing a body keeps the declarations.* A module with the body
of a function replaced declares each symbol for the same types as the
module does: replacing a body changes no external declaration.
:::

:::readable Fir.Module.callable_replaceBody (pin := Fir.Module.callable) (fingerprint := "8045198629372872118")
*Theorem: replacing a body keeps what the module can call.* For every
symbol $`s`, region $`b`, types $`t^*` and $`r^*`, and symbol $`x`,
$`\mathrm{callable}_{M[s \leftarrow b]}(t^*, r^*)(x) = \mathrm{callable}_M(t^*, r^*)(x)`:
every function keeps its parameter and result types, and every external
declaration stays.
:::

:::readable Fir.Module.symbols_replaceBody Fir.Module.context_replaceBody Fir.Module.dialectItems_replaceBody Fir.Module.aggregates_replaceBody Fir.Module.layouts_replaceBody Fir.Module.globals_replaceBody Fir.Module.externs_replaceBody (pin := Fir.Module.symbols) (pin := Fir.Module.context) (fingerprint := "4504637312167593682")
*Theorems: a replacement keeps the symbol table and the context of
validation.* For every module $`M`, symbol $`s` and region $`b`, the
{ref "The-fir-specification--Validation--Scope-and-symbols"}[symbol table]
of $`M[s \leftarrow b]` is that of $`M`, since every function keeps its
symbol and its type; so is the context in which validation checks its
functions, which is the symbol table, the keys of the location table and
the layouts and globals of its own table. The items of a dialect's kind of its own
table, its aggregates' layouts, its globals and its external declarations
are those of $`M`, and so are the layouts as the rule of an op sees them.
:::

:::readable Fir.Item.name_replaceBody Fir.Item.tablesIn_replaceBody (fingerprint := "3259367735023084775")
*Theorems: replacing a body keeps the symbols and the nested tables.* For
every symbol $`s`, region $`b` and item $`i`, the item with the body
replaced has the symbol of $`i`. For every list of items, the items with
the body replaced hold the same
{ref "The-fir-specification--Validation--Scope-and-symbols"}[symbol tables]:
a function holds none, and a nested module is unchanged.
:::

:::readable Fir.Module.valid_replaceBody (pin := Fir.Module.Valid) (fingerprint := "18278698334459200132")
*Theorem: a valid module stays valid when the new function is valid.* For
every dialect with its validation rules, let $`M` be a
{ref "The-fir-specification--Validation--The-general-rules"}[valid module],
$`s` a symbol and $`b` a region, and let each function $`g` of $`M` with
the symbol $`s`, given the body $`b`, be valid in the context of $`M`, with
each of its types, and each type that its ops carry in their attributes,
naming a memory that the layout of $`M` declares, and each pair
$`(N, V)` that its ops ask, $`\mathrm{opunits}`, naming a memory whose
units in the layout of $`M` are $`V` bits wide, and each pair $`(N, W)`
that its ops ask, $`\mathrm{opaddrs}`, naming an integral memory whose
pointers in the layout of $`M` are $`W` bits wide. Then
$`M[s \leftarrow b]` is valid: the symbols of its own table are those of
$`M`, so still unique; its location table, its dialect set and its layout
are those of $`M`; each of its functions is valid in its context, which is
that of $`M`, its types name memories of the layout, its ops' values are
as wide as their memories' units, and its ops' integers as wide as their
memories' pointers; its aggregates'
layouts and its globals are those of $`M`, so still valid; and its nested
modules, and so
the tables they hold, are those of $`M`.

So the new body needs to be checked alone, against the old module's
symbol table; every other function was already valid there.
:::
