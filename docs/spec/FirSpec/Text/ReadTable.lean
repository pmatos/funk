import VersoManual
import Fir.Text.ReadTable
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the location table read back, which
renders `Fir.Text.ReadTable` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The location table read back: readable blocks" =>

:::moduleDocs (fingerprint := "4937616668860296335")
:::

:::readable Fir.Text.readNat_cons (pin := Fir.Text.readNat) (pin := Fir.Location.limit) (fingerprint := "10446730023852332739")
*Theorem: a line or a column in range reads back.* For every number
$`n < 2^{32}`, the
{ref "The-fir-specification--Text-format--Reading-the-location-table-and-the-module"}[reader of a line or a column],
whatever name and position it would report in an error, reads the
{ref "The-fir-specification--Text-format--The-parser"}[token]
$`\mathsf{int}~n` at the front of any tokens as $`n`, and leaves the tokens
after it. A larger number is an error, so the bound is needed.
:::

:::readable Fir.Text.readLocRef_cons Fir.Text.readLocRef_reads (pin := Fir.Text.readLocRef) (fingerprint := "664681862593415093")
*Theorems: a location reference inside a location reads back.* For every
location reference $`r` and every position, the reader of a location
reference reads $`\mathsf{locref}~r` at the front of any tokens as $`r`,
and leaves the tokens after it. So it
{ref "The-fir-specification--Text-format--The-grammar-step"}[reads]
$`\mathsf{locref}~r` as $`r` before any token but `(`, the form that the
reader of the rest of a list needs.
:::

:::readable Fir.Text.Location.reads (pin := Fir.Text.readLocation) (pin := Fir.Text.readRange) (pin := Fir.Text.readLocArgs) (pin := Fir.Location.tokens) (pin := Fir.Location.numbers) (pin := Fir.Location.limit) (pin := Fir.Location.refs) (pin := Fir.Text.readNat) (fingerprint := "126514208146092090")
*Theorem: a location reads back.* For every
{ref "The-fir-specification--Abstract-syntax--Locations"}[location]
$`\mathit{loc}` each of whose numbers is below $`2^{32}`, the reader of a
location reads the
{ref "The-fir-specification--Text-format--Lexing-printed-text"}[tokens of $`\mathit{loc}`]
as $`\mathit{loc}`, before any token.

The numbers of a location are the lines and columns of a source range, or
the location references of a location built from others. The reader checks
the bound on lines and columns; no reader checks it on references, which
read back whatever their value. Every kind of location ends with a token
that its reader takes alone, a number, `)` or the word `unknown`, so what
follows does not matter.
:::

:::readable Fir.Text.readLocEntries_reads (pin := Fir.Text.readLocEntries) (pin := Fir.LocTable.InLimits) (pin := Fir.Location.numbers) (pin := Fir.Location.limit) (fingerprint := "1442921532955444180")
*Theorem: the entries of a location table read back.* For every location
table $`t`
{ref "The-fir-specification--Abstract-syntax--Locations"}[within limits],
whose references, lines and columns are all below $`2^{32}`, the reader
of the table's entries reads
$`\mathsf{locref}~r~\texttt{=}~\mathrm{tokens}(\mathit{loc})`, for each
entry $`r = \mathit{loc}` of $`t` in order, as $`t`, before `}`. It reads
entries as long as a location reference follows, so the `}` stops it.
:::

:::readable Fir.Text.LocTable.reads (pin := Fir.Text.readLocs) (pin := Fir.LocTable.tokens) (pin := Fir.LocTable.InLimits) (fingerprint := "8712453982098762322")
*Theorem: a location table reads back.* For every location table $`t`
{ref "The-fir-specification--Abstract-syntax--Locations"}[within limits],
the reader of the location table reads its tokens,
$`\mathsf{word}~\mathtt{locs}~\texttt{\{}`, its entries and
$`\texttt{\}}`, as $`t`, before any token.
:::
