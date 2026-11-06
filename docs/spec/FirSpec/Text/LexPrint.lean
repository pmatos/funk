import VersoManual
import Fir.Text.LexPrint
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on attributes, locations and names,
which renders `Fir.Text.LexPrint` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Attributes, locations and names: readable blocks" =>

:::readable Fir.toString_string (fingerprint := "8085136495838143184")
*Lemma: a string, converted to a string, is itself.* The printer builds
some text with a conversion to a string, and this lets the proofs read the
text it gives as the string itself.
:::

:::readable Fir.Attr.spells Fir.Attr.spellsEach (pin := Fir.Attr.print) (pin := Fir.Attr.print.printList) (pin := Fir.Attr.tokens) (pin := Fir.Attr.tokens.tokensList) (fingerprint := "6864249825547241286")
*Theorems: a printed attribute spells its tokens.* For every
{ref "The-fir-specification--Text-format--Grammar"}[attribute] $`a`, or
type, whose
{ref "The-fir-specification--Text-format--Lexing-printed-text"}[tokens]
can all be written:

$$`\mathrm{spells}(\mathrm{print}(a), \mathrm{tokens}(a))`

The printer writes a word, an integer, a string and a symbol as the
spelling of its one token, and an application $`h(a_1, \dots, a_n)` as the
word $`h`, then `(`, the printed arguments with `, ` between them, and
`)`. So for every list of attributes whose tokens can all be written, the
printed attributes spell their tokens one by one; the two are proved
together, since an argument may itself be an application.
:::

:::readable Fir.Location.spells (pin := Fir.Location.print) (pin := Fir.Location.tokens) (fingerprint := "7007539334904954082")
*Theorem: a printed location spells its tokens.* For every
{ref "The-fir-specification--Abstract-syntax--Locations"}[location]
$`\mathit{loc}` whose tokens can all be written:

$$`\mathrm{spells}(\mathrm{print}(\mathit{loc}), \mathrm{tokens}(\mathit{loc}))`

The printer writes a location as `unknown`, `"file":l:c to l:c`,
`name("n")`, `callsite(@r at @r)`, `fused(@r, …)` or `derived(@r)`. A
range has no space around its colons: after the quoted file, a `:` is
punctuation, and after a line, the `:` that follows is not a name
character, so the line is read whole.
:::

:::readable Fir.spells_def Fir.spells_defs (pin := Fir.printDef) (pin := Fir.printDefs) (fingerprint := "811370583130359941")
*Theorems: printed definitions spell their tokens.* For every dialect with
a {ref "The-fir-specification--Text-format--Grammar"}[text format]:

* every definition $`x : T` of a value whose tokens can all be written
  is printed as `%`, $`x`, `: ` and the type written as an attribute, and
  that text spells its tokens;
* every list of definitions whose tokens can all be written is printed
  with `, ` between them, and that text spells its tokens.
:::

:::readable Fir.spells_use (fingerprint := "8123692740036956647")
*Theorem: a use of a value spells its token.* For every
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[name]
$`x`, `%` then $`x` spells $`\mathsf{value}~x`. The printer writes each
operand of an op and each argument of a successor this way.
:::

:::readable Fir.Succ.spells (pin := Fir.Succ.print) (pin := Fir.Succ.tokens) (fingerprint := "18443835119475044151")
*Theorem: a printed successor spells its tokens.* For every successor
$`\ell(a_1, \dots, a_n)` whose tokens can all be written: it is printed as
`^` then $`\ell` when $`n = 0`, and otherwise as `^`, $`\ell`, `(`, the
uses `%`$`a_i` with `, ` between them, and `)`; that text spells its
tokens.
:::
