import VersoManual
import Fir.Text.PrintParse
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the round trip, proved, which renders
`Fir.Text.PrintParse` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The round trip, proved: readable blocks" =>

:::moduleDocs (fingerprint := "7816641951814192479")
:::

:::readable Fir.printThenParse Fir.parseThenPrint (pin := Fir.PrintThenParse) (pin := Fir.ParseThenPrint) (pin := Fir.parse) (fingerprint := "6498295009264724367")
*Theorems: both round trips hold for the parser.* For every dialect with
signatures, validation rules and a text format whose text is
{ref "The-fir-specification--Text-format--Grammar"}[lawful], the
{ref "The-fir-specification--Text-format--Decoding"}[parser] meets
{ref "The-fir-specification--Text-format--Round-trips"}[both round trips]:

* _print then parse_: for every well-formed module $`m`,
  $`\mathrm{parse}(\mathrm{print}(m)) = m`;
* _parse then print_: for every well-formed module $`m_0` and every module
  $`m`, if $`\mathrm{parse}(\mathrm{print}(m_0)) = m` then
  $`\mathrm{print}(m) = \mathrm{print}(m_0)`.

The first is the three steps put together. The lexer reads
$`\mathrm{print}(m)` as the tokens of $`m`, then the grammar reads them as
a tree that
{ref "The-fir-specification--Text-format--The-module-read-back"}[erases to the tree of $`m`],
and decoding gives $`m` back from
{ref "The-fir-specification--Text-format--The-module-decoded-back"}[any such tree].
The second follows from the first.
:::

:::readable Fir.Module.WellFormed.parse_print Fir.Module.WellFormed.print_injective Fir.Module.WellFormed.print_inj (pin := Fir.Module.print) (fingerprint := "8986024461800127046")
*Theorems: a well-formed module reads back, and its text names it.* For
every dialect with signatures, validation rules and a lawful text, and all
well-formed modules $`m`, $`m_1` and $`m_2`:

* parsing the printed text of $`m` gives $`m`;
* if $`m_1` and $`m_2` print the same text, then $`m_1 = m_2`;
* $`m_1` and $`m_2` print the same text exactly when $`m_1 = m_2`.

The last two make the text a faithful name for a well-formed module: tools
can compare such modules by comparing their text.
:::

:::readable Fir.Module.Valid.parse_print Fir.Module.Valid.print_injective (pin := Fir.Module.Valid) (fingerprint := "12063138789887651199")
*Theorems: a valid module reads back, and its text names it.* For every
dialect with signatures, validation rules and a lawful text, and all
{ref "The-fir-specification--Validation--The-general-rules"}[valid]
modules $`m`, $`m_1` and $`m_2`:

* parsing the printed text of $`m` gives $`m`;
* if $`m_1` and $`m_2` print the same text, then $`m_1 = m_2`.

Every valid module of such a dialect is
{ref "The-fir-specification--Text-format--Round-trips"}[well formed], so
both follow from the theorems for well-formed modules.
:::

:::readable Fir.Core.printThenParse Fir.Core.parseThenPrint Fir.Core.print_injective (fingerprint := "9974484314842745829")
*Theorems: both round trips hold for the core dialect, and its valid
modules print differently.* For the
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[core dialect]:

* print then parse holds for the parser: for every well-formed module
  $`m`, $`\mathrm{parse}(\mathrm{print}(m)) = m`;
* parse then print holds for the parser;
* two valid modules that print the same text are the same module.

The core dialect's text is
{ref "The-fir-specification--Text-format--The-core-dialect___s-text-is-lawful"}[lawful],
so these are the theorems above, for the core dialect.
:::
