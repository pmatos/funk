import VersoManual
import Fir.Text.Print
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the canonical printer, which renders
`Fir.Text.Print` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "The canonical printer: readable blocks" =>

:::moduleDocs (fingerprint := "3900405696603947115")
:::

:::readable Fir.Attr.print (pin := Fir.Text.quote) (pin := Fir.Text.printInt) (pin := Fir.Text.printSymbol) (fingerprint := "17301581164338892305")
*Definition: an attribute in text.* The text of an
{ref "The-fir-specification--Text-format--Grammar"}[attribute] $`a`,
$`\mathrm{print}(a)`, is:

$$`\begin{aligned} \mathrm{print}(\mathsf{word}~w) &= w \\ \mathrm{print}(\mathsf{int}~i) &= \mathrm{printint}(i) \\ \mathrm{print}(\mathsf{str}~s) &= \mathrm{quote}(s) \\ \mathrm{print}(\mathsf{sym}~s) &= \mathrm{printsym}(s) \\ \mathrm{print}(\mathsf{app}~h~a_1 \dots a_n) &= h\,\texttt{(}\,\mathrm{print}(a_1)\texttt{,} \\ &\quad \dots\texttt{,}~\mathrm{print}(a_n)\,\texttt{)} \end{aligned}`

where $`\mathrm{printint}(i)`, $`\mathrm{quote}(s)` and $`\mathrm{printsym}(s)` are
the one spelling of an integer, a string and a symbol, from the
{ref "The-fir-specification--Text-format--Tokens"}[tokens section]. The
arguments of an applied attribute are separated by a comma and a space, and
`h()` is printed for $`n = 0`. A type is printed the same way, as the
attribute that its dialect writes it as.
:::

:::readable Fir.printLocRef Fir.Location.print (pin := Fir.Location) (pin := Fir.Text.quote) (fingerprint := "7699129085592594488")
*Definition: a location reference and a location in text.* The
{ref "The-fir-specification--Abstract-syntax--Locations"}[location reference]
$`r` is written `@` followed by $`r` in decimal. Each location is written
as the location table shows it, with each string quoted and each reference
written as above:

* $`\mathsf{unknown}` is `unknown`;
* $`\mathsf{range}~\mathit{file}~l_1~c_1~l_2~c_2` is
  `"file":l₁:c₁ to l₂:c₂`, with no spaces around the colons;
* $`\mathsf{name}~n` is `name("n")`;
* $`\mathsf{callsite}~r_1~r_2` is `callsite(@r₁ at @r₂)`;
* $`\mathsf{fused}~r_1 \dots r_n` is `fused(@r₁, …, @rₙ)`, and `fused()`
  when $`n = 0`;
* $`\mathsf{derived}~r` is `derived(@r)`.
:::

:::readable Fir.indent Fir.printDef Fir.printDefs Fir.Succ.print (pin := Fir.Succ) (fingerprint := "6199687798288357607")
*Definition: indentation, definitions and successors in text.*
$`\mathrm{indent}(n)` is $`n` spaces. A definition of the value $`x` with
the type $`t` is written `%x: T`, where `T` is the attribute that the
{ref "The-fir-specification--Text-format--Grammar"}[dialect writes]
$`t` as, printed. A list of definitions is written with a comma and a space
between each two. A
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[successor]
to the block $`\ell` that passes $`x_1, \dots, x_n` is written
`^ℓ(%x₁, …, %xₙ)`, and `^ℓ` when $`n = 0`.
:::

:::readable Fir.printKind Fir.Operation.print Fir.Region.printList Fir.Block.printList Fir.Operation.printList (pin := Fir.Operation) (pin := Fir.Block) (fingerprint := "10544776060343288224")
*Definition: an op, with its regions and their blocks, in text.* An op at
the indentation $`n` is one line, made of, in order:

* $`\mathrm{indent}(n)`;
* when the op has results, their definitions, then ` = `;
* the op's name, then each of its attributes, each after one space;
* when the op has operands or successors, one space, then the operands as
  `%x`, then the successors, all separated by a comma and a space;
* for each region of the op, ` {`, then one space and the region's kind
  when it names one, a line feed, the region's blocks at the indentation
  $`n + 2`, then $`\mathrm{indent}(n)` and `}`;
* one space, the op's location reference, and a line feed.

A block with the label $`\ell` at the indentation $`n` is a line of
$`\mathrm{indent}(n)` and `^ℓ:`, or `^ℓ(%x: T, …):` with the definitions
of its arguments when it has any, followed by its ops at the indentation
$`n + 2`. A list of blocks, or of ops, is each of them in turn.
So `%s: i32 = add nsw %a, %b @3` is an op at the indentation 2 with one
result, one attribute, two operands and the location reference 3.
:::

:::readable Fir.Func.print Fir.Item.print (pin := Fir.Text.printSymbol) (fingerprint := "5954500298775366958")
*Definition: a function, and an item, in text.* A function with the symbol
$`s`, the parameters $`p^*`, the result types $`t_1, \dots, t_n` and the
body $`b^*` is written:

* `func`, a space, $`\mathrm{printsym}(s)`, then its parameters' definitions in
  parentheses, with no space before them: `func @sum(%n: i32)`;
* when $`n > 0`, ` -> ` and the result types, separated by a comma and a
  space;
* ` {`, a line feed, its blocks at the indentation 0, then `}` and a line
  feed.

An item that is a function is written as that function. A `func` has no
attributes, so none are printed.
:::

:::readable Fir.LocTable.print Fir.printDialects Fir.Module.print (fingerprint := "3877336929970104377")
*Definition: the location table, and a module, in text.* The
{ref "The-fir-specification--Abstract-syntax--Locations"}[location table]
is written `locs {` and a line feed, then each entry $`r = \mathit{loc}`
in the order the table stores them, as the line `  @r = loc`, indented by
two spaces, then `}` and a line feed. The dialect set $`x_1, \dots, x_n`
of a module is written `dialects x₁, …, xₙ` and a line feed, then an empty
line, and nothing when $`n = 0`. A module is its dialect set, then each of
its items, followed by an empty line, and then its location table. So every
text ends with a line feed, and a module with no dialects and no items is
`locs {` and `}` on two lines. The
{ref "The-fir-specification--Text-format--Example"}[example] shows a
module in this layout.
:::
