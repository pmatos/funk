import VersoManual
import Fir.Text.ReadLocs
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on reading the location table and the
module, which renders `Fir.Text.ReadLocs` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Reading the location table and the module: readable blocks" =>

:::moduleDocs (fingerprint := "1149782529116021061")
:::

:::readable Fir.Text.readNat Fir.Text.readLocRef (pin := Fir.Location.limit) (fingerprint := "14401333200745503308")
*Definition: reading the numbers of a location.* A line or a column is an
integer token that is not negative, and must be below $`2^{32}`: a larger
one is an error at the number, such as "a line 4294967296 is out of range:
it must be below 2^32". Any other token there is an error, "expected a
line" or "expected a column". A location reference inside a location is a
location reference token, whose bound the lexer has checked.
:::

:::readable Fir.Text.readRange Fir.Text.readLocArgs Fir.Text.readLocation (pin := Fir.Location) (fingerprint := "14500707900668292005")
*Definition: reading a location.* A
{ref "The-fir-specification--Abstract-syntax--Locations"}[location] is
read by its first token:

* a string, the file, starts a source range, `"file":l₁:c₁ to l₂:c₂`: the
  file, `:`, a line, `:`, a column, the word `to`, a line, `:` and a
  column;
* the word `unknown` is the unknown location;
* the words `name`, `callsite`, `fused` and `derived` are followed by
  `(`, what the kind holds, and `)`: a string for `name`, a location
  reference, the word `at` and a location reference for `callsite`, a
  location reference for `derived`, and for `fused` location references
  separated by commas, which may be none;
* any other word is an error at it, "is not a kind of location", and any
  other token is an error, "expected a location".
:::

:::readable Fir.Text.readLocEntries Fir.Text.readLocs (fingerprint := "9556671690069463874")
*Definition: reading the location table.* The table is the word `locs`,
then `{`, then its entries, then `}`. An entry is a location reference,
`=` and a location, and entries are read as long as a location reference
follows. The entries are kept in the order they are written; whether
their references increase is checked by validation, not here.
:::

:::readable Fir.Text.readModule (pin := Fir.Text.readDialects) (fingerprint := "14734074965958306714")
*Definition: reading a module.* A module is its dialect set, then its
items, read at the top level, then its location table, which must start with the word `locs`,
then the end of the text. Anything else after the items is an error,
"expected an item or the location table", and anything after the table is
an error, "expected the end of the text after the location table".
:::
