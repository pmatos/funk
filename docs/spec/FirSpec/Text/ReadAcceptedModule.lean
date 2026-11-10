import VersoManual
import Fir.Text.ReadAcceptedModule
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on an accepted location table, which
renders `Fir.Text.ReadAcceptedModule` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "An accepted location table: readable blocks" =>

:::moduleDocs (fingerprint := "6064928561908290930")
:::

:::readable Fir.Text.readNat_writable Fir.Text.readLocRef_writable (pin := Fir.Text.readNat) (pin := Fir.Text.readLocRef) (pin := Fir.Location.limit) (fingerprint := "5781592515716110835")
*Theorems: a line, a column and a reference as read are below
$`2^{32}`.* For every list of tokens:

* the reader of a line or a column
  {ref "The-fir-specification--Text-format--What-the-grammar-accepts"}[gives]
  that the number it reads is below $`2^{32}`, whatever the label that its
  error messages use, such as "a line". The lexer does not bound
  an integer token, so the reader checks it: it reads an integer token
  $`n \ge 0` only when $`n < 2^{32}`, and is an error at the number
  otherwise;
* the reader of a location reference inside a location gives that the
  reference is below $`2^{32}`: it comes from a location reference token,
  which the lexer bounds.
:::

:::readable Fir.Text.readRange_writable Fir.Text.readLocArgs_writable Fir.Text.readLocation_writable (pin := Fir.Text.readRange) (pin := Fir.Text.readLocArgs) (pin := Fir.Text.readLocation) (pin := Fir.Location.InLimits) (pin := Fir.Location.numbers) (pin := Fir.Location.refs) (fingerprint := "13677558438606440226")
*Theorems: a location as read is within the limits.* For every list of
tokens:

* for every file, the reader of a source range after its file gives that
  the range is
  {ref "The-fir-specification--Text-format--What-the-grammar-accepts"}[within the limits]:
  its two lines and two columns are each read as a line or a column, so
  each is below $`2^{32}`;
* for every kind of location, the reader of the part of the location in
  parentheses gives that it is within the limits: the references of a
  $`\mathsf{callsite}`, $`\mathsf{fused}` or $`\mathsf{derived}` location
  are each read as a location reference, and a $`\mathsf{name}` location
  holds no number;
* the reader of a
  {ref "The-fir-specification--Abstract-syntax--Locations"}[location]
  gives that it is within the limits; $`\mathsf{unknown}` holds no number.
:::

:::readable Fir.Text.readLocEntries_writable Fir.Text.readLocs_writable (pin := Fir.Text.readLocEntries) (pin := Fir.Text.readLocs) (pin := Fir.LocTable.InLimits) (fingerprint := "17027887153305260957")
*Theorems: the location table as read is within the limits.* For every
list of tokens, the reader of the entries of the location table, and the
reader of the whole table, `locs` `{` and its entries `}`, give that the
table they read is within the limits: the key of each entry comes from a
location reference token, and its location is within the limits. So every
number of the table is below $`2^{32}`.
:::

:::readable Fir.Text.readModule_writable (pin := Fir.Text.readModule) (pin := Fir.Text.SModule.Writable) (pin := Fir.Text.TokensWritable) (fingerprint := "18411574549067702597")
*Theorem: the grammar step.* For every list of tokens $`\mathit{ts}` that
{ref "The-fir-specification--Text-format--What-the-lexer-accepts"}[can be written],
and every module $`s` as read: when the
{ref "The-fir-specification--Text-format--Reading-the-location-table-and-the-module"}[reader of a module]
reads $`s` from $`\mathit{ts}`, $`s` can be written:

$$`\begin{aligned} & \mathrm{writable}(\mathit{ts}) \wedge \mathrm{readmodule}(\mathit{ts}) = \mathsf{ok}(s) \\ & \quad \implies s \text{ can be written} \end{aligned}`

Here $`\mathrm{readmodule}(\mathit{ts}) = \mathsf{ok}(s)` says that the
reader of a module reads $`s` from $`\mathit{ts}` without an error, and
$`s` can be written when the names of its dialect set are words, each of
its items can be written and its location table is within the limits. The
reader reads the dialect set, then the items, then the table, then
$`\mathsf{eof}`. With the lexer's step, the first two steps of the parser
give a module as read that can be written, from every text that they
accept.
:::
