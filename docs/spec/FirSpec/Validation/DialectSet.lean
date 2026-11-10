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

:::moduleDocs (fingerprint := "11037091894869912644")
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

:::readable Fir.Module.InDialectSet (fingerprint := "16180865123344886961")
*Definition: a module keeps to its dialect set.* A module $`m` of the
dialect $`d` keeps to its dialect set $`\mathrm{set}(m)` when

* every dialect $`x \in \mathrm{set}(m)` is in $`\mathrm{names}(d)`: the
  module names only dialects that $`d` holds, and never the core, whose
  name is in no set;
* for every function $`f` of $`m`, every dialect that the words of $`f`
  name is in $`\mathrm{set}(m)`.

So a module that names no dialect writes only the core's words.
:::

:::readable Fir.Func.setProblems Fir.Module.setProblems (fingerprint := "11442657290716343393")
*Definition: the check of a module's dialect set.* The check gives, in
order: "the dialect set names $`x`, which is not a known dialect" for each
dialect $`x` of the set that $`d` does not hold; then, for each function,
one problem when its words name a dialect outside the set: "the function
writes a word of the dialect $`x`, which the module's dialect set does not
name", for the first such dialect $`x` in the order of the function's
words.
:::

:::readable Fir.Module.setProblems_eq_nil_iff (fingerprint := "1590659387001300546")
*Theorem: the check decides the rule.* For every module $`m`, the check of
its dialect set gives no problem exactly when $`m` keeps to its set:

$$`\mathrm{setProblems}(m) = [\,] \iff m \text{ keeps to its dialect set}`

A function's one problem stands for every word outside the set: the check
finds the first, and there is none exactly when every word is in the set.
So whether a module keeps to its set can be decided.
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
