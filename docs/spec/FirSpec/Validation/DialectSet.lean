import VersoManual
import Fir.Validation.DialectSet
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a module's dialect set, which renders
`Fir.Validation.DialectSet` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "A module's dialect set: readable blocks" =>

:::moduleDocs (fingerprint := "11077141747893955975")
:::

:::readable Fir.opDialects Fir.Func.wordDialects (fingerprint := "15713263119767034989")
*Definition: the dialects that a function's words name.* The dialects of an
op instance $`p` are those of its name and then those of its attributes:

$$`\mathrm{dialects}(p) = \mathrm{dialect}(\mathrm{opname}(p)) \mathbin{+\!\!+} \mathrm{dialects}(\mathrm{opattrs}(p))`

where a bare name gives none. The dialects of a function $`f` are, in
order, those of the words of each type that $`f` states, its result types
and the type of each value it defines, and then those of each op of its
blocks, at any depth.
:::

:::readable Fir.SymbolTable.InDialectSet Fir.Module.InDialectSet (fingerprint := "13360016989078555249")
*Definition: a module keeps to its dialect sets.* A
{ref "The-fir-specification--Validation--Scope-and-symbols"}[symbol table]
$`T` of a module of the dialect $`d` keeps to its dialect set
$`\mathrm{dialects}(T)` when

* every dialect $`x \in \mathrm{dialects}(T)` is in $`\mathrm{names}(d)`:
  the table names only dialects that $`d` holds, and never the core, whose
  name is in no set;
* for every function $`f` of $`T`, every dialect that the words of $`f`
  name is in $`\mathrm{dialects}(T)`.

A module $`m` keeps to its dialect sets when each of its tables does: its
own, and that of each nested module, at any depth. A nested module's set is
its own, not its parent's (ADR-2026-11-10-1510). So a table that names no
dialect writes only the core's words, whatever its parent names, and a
parent's set does not name the dialects of a nested module's set.
:::

:::readable Fir.Func.setProblems Fir.SymbolTable.setProblems Fir.Module.setProblems (fingerprint := "16659464722050661835")
*Definition: the check of a module's dialect sets.* The check of a table
gives, in order: "the dialect set names $`x`, which is not a known dialect"
for each dialect $`x` of its set that $`d` does not hold; then, for each of
its functions, one problem when its words name a dialect outside the set:
"the function writes a word of the dialect $`x`, which the module's dialect
set does not name", for the first such dialect $`x` in the order of the
function's words. The check of a module gives the problems of each of its
tables, in order.
:::

:::readable Fir.SymbolTable.setProblems_eq_nil_iff Fir.Module.setProblems_eq_nil_iff (fingerprint := "556859963236241723")
*Theorem: the check decides the rule.* For every table $`T`, the check of
its dialect set gives no problem exactly when $`T` keeps to its set, and so,
for every module $`m`:

$$`\mathrm{setProblems}(m) = [\,] \iff m \text{ keeps to its dialect sets}`

A function's one problem stands for every word outside the set: the check
finds the first, and there is none exactly when every word is in the set.
So whether a module keeps to its sets can be decided.
:::

:::readable Fir.Module.ValidInSet Fir.Module.allProblems (fingerprint := "1503219130715903302")
*Definition: a module that passes validation, and all its problems.* A
module passes validation with its dialect set when it is valid and keeps to
its set. Its problems are those of the validation check, then those of its
dialect set. `fir-ref validate` and `funk verify` report both.
:::

:::readable Fir.Module.allProblems_eq_nil_iff (fingerprint := "8219969930551526190")
*Theorem: a module has no problem exactly when it passes validation.* For
every module $`m` of a dialect whose rules are decidable,

$$`\mathrm{allProblems}(m) = [\,] \iff m \text{ is valid and keeps to its dialect set}`

So whether a module passes validation with its dialect set can be decided.
:::
