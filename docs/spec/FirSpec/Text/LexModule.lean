import VersoManual
import Fir.Text.LexModule
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on ops, functions and the module, which
renders `Fir.Text.LexModule` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Ops, functions and the module: readable blocks" =>

:::moduleDocs (fingerprint := "4529290017172724994")
:::

:::readable Fir.spells_lhs (pin := Fir.printDefs) (fingerprint := "7259325238878645560")
*Theorem: an op's results and its `=` spell their tokens before any
characters.* For every dialect with a
{ref "The-fir-specification--Text-format--Grammar"}[text format] and every
list of definitions $`d^*`, if the tokens below can all be written: the
text that the printer writes before an op's name, which is empty when
$`d^*` is empty, and otherwise the printed definitions $`d^*` then ` = `,
{ref "The-fir-specification--Text-format--Spaces___-line-feeds-and-lists"}[spells before any characters]
the empty list of tokens, or the tokens of
$`d^*` then $`\texttt{=}`.
:::

:::readable Fir.spells_rhs (fingerprint := "1330297367071894883")
*Theorem: an op's name, attributes, operands and successors spell their
tokens.* For every dialect with a text format, op instance $`o`, operands
$`x_1, \dots, x_m` and successors $`s_1, \dots, s_k`, if their tokens below
can all be written: the text that the printer writes for them spells
$`\mathsf{word}~n` for the name $`n` of $`o`, the tokens of the attributes of $`o`,
then, when $`m + k > 0`, the uses and the successors' tokens with
$`\texttt{,}` between them. The text is the name of $`o` and its printed
attributes with a space between each, then, when $`m + k > 0`, a space,
and the uses `%`$`x_i` and the printed successors with `, ` between them.
:::

:::readable Fir.boundary_regions (pin := Fir.Region.printList) (fingerprint := "10175431880597102562")
*Theorem: an op's regions, then a space, are at the end of a token.* For
every dialect with a text format, indentation $`n`, list of regions and
characters $`c`: the printed regions, then a space, then $`c`, are
{ref "The-fir-specification--Text-format--Maximal-munch"}[at the end of a token]. A printed region starts with ` {`, so either way the text
starts with a space; this is what lets an op's last attribute, operand or
successor be read whole before it.
:::

:::readable Fir.Operation.spells Fir.Region.spellsList Fir.Block.spellsList Fir.Operation.spellsList (pin := Fir.Operation.print) (pin := Fir.Region.printList) (pin := Fir.Block.printList) (pin := Fir.Operation.printList) (fingerprint := "3306766056893596332")
*Theorems: printed ops, regions and blocks spell their tokens before any
characters.* For every dialect with a text format and every indentation
$`n`:

* every op $`o` whose tokens can all be written, printed at indentation
  $`n`, spells $`\mathrm{tokens}(o)` before any characters;
* so does every list of regions of an op at indentation $`n`, every list
  of blocks at indentation $`n`, and every list of ops at indentation
  $`n`, whose tokens can all be written.

The
{ref "The-fir-specification--Text-format--The-canonical-printer"}[printer]
writes an op on a line of its own: its indentation, its results and
` = `, its name, attributes, operands and successors, its regions, a
space, its location reference and a line feed. A region is ` {`, a line
feed, its blocks two spaces deeper, the op's indentation and `}`. A block
is its indentation, `^` and its label, its arguments in parentheses when
it has any, `:`, a line feed and its ops two spaces deeper. Each ends with
a line feed or a `}`, which is why each spells its tokens before any
characters. The four are proved together, since ops hold regions, which
hold blocks of ops.
:::

:::readable Fir.Func.spells Fir.Item.spells (pin := Fir.Func.print) (pin := Fir.Item.print) (fingerprint := "3754463180754474539")
*Theorems: a printed function, and an item, spell their tokens before any
characters.* For every dialect with a text format, every function $`f`
whose tokens can all be written spells $`\mathrm{tokens}(f)` before any
characters, printed as `func`, a space, its symbol, its parameters in
parentheses, ` -> ` and its result types with `, ` between them when it
has results, ` {`, a line feed, its blocks, `}` and a line feed. So does
every item whose tokens can all be written.
:::

:::readable Fir.LocTable.spellsEntries Fir.LocTable.spells (pin := Fir.LocTable.print) (fingerprint := "6259925923906660465")
*Theorems: the printed location table spells its tokens before any
characters.* For every location table whose tokens can all be written:

* its entries, each printed as two spaces, the location reference, ` = `,
  the printed location and a line feed, spell before any characters the
  tokens $`\mathsf{locref}~r~\texttt{=}~\mathrm{tokens}(\mathit{loc})` of
  each entry $`r = \mathit{loc}`;
* the table, printed as `locs {`, a line feed, its entries, `}` and a
  line feed, spells its tokens before any characters.
:::

:::readable Fir.spellsDialects (pin := Fir.printDialects) (pin := Fir.dialectsTokens) (fingerprint := "11569368363644327681")
*Theorem: a printed dialect set spells its tokens before any characters.*
For every list of names whose tokens can all be written, so whose names are
words, its printed form spells its tokens before any characters: nothing,
when the list is empty, and otherwise the word `dialects`, a space, the
names separated by a comma and a space, and two line feeds.
:::

:::readable Fir.Module.spellsItems Fir.Module.spells (pin := Fir.Module.print) (fingerprint := "4621242517318431203")
*Theorems: a printed module spells its tokens before any characters.* For
every dialect with a text format:

* every list of items whose tokens can all be written, each printed then
  followed by an empty line, spells before any characters the tokens of
  the items;
* every module $`m` whose tokens can all be written, printed as its
  dialect set, its items and then its location table, spells
  $`\mathrm{tokens}(m)` before any characters.
:::

:::readable Fir.lex_print (pin := Fir.Text.lex) (pin := Fir.Module.tokens) (pin := Fir.Text.Tok.Writable) (fingerprint := "7324819918049803602")
*Theorem: lexing printed text gives its tokens.* For every dialect with a
text format and every module $`m` whose tokens can all be
{ref "The-fir-specification--Text-format--Lexing-printed-text"}[written],
the {ref "The-fir-specification--Text-format--The-parser"}[lexer] reads
the printed text of $`m` without error, and gives exactly the tokens of
$`m`, then $`\mathsf{eof}`, positions aside:

$$`\overline{\mathrm{lex}(\mathrm{print}(m))} = \mathrm{tokens}(m)~\mathsf{eof}`

Here $`\overline{u}` drops the positions of the tokens $`u`. The positions
are the lexer's own; the grammar step of the parser reads the tokens at
any positions, so this is all it needs. The proof applies the previous
theorem to the empty text that follows the module, which lexes to no
token.
:::
