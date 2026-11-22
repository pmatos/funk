import VersoManual
import Fir.Text.ReadFunc
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a function read back, which renders
`Fir.Text.ReadFunc` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "A function read back: readable blocks" =>

:::moduleDocs (fingerprint := "17697587987197129415")
:::

:::readable Fir.bind_reads (fingerprint := "11770048284880457070")
*Lemma: proof plumbing for one step followed by another.* Let $`X` be a
step that may fail, and $`K` what runs on its result. If $`X` succeeds with
a result that has a property $`Q`, and $`K` succeeds with a result that
has a property $`P` from every result with $`Q`, then $`X` followed by
$`K` succeeds with a result that has $`P`. The proof below uses it to take
the reader of an item one part at a time.
:::

:::readable Fir.Func.paramsTokens_eq (fingerprint := "9774148740466177528")
*Lemma: a function's parameters as the reader of parameters takes them.*
For every dialect with a text format and every function $`f`, the tokens
of the parameters of $`f` are those of its parameters paired with their
attributes, ending in `...` when $`f` is variadic, as the reader of
parameters writes them.
:::

:::readable Fir.Func.readsAs Fir.Func.reads (pin := Fir.Text.readItem) (pin := Fir.Func.tokens) (pin := Fir.Func.types) (pin := Fir.Func.defs) (pin := Fir.Func.allBlocks) (fingerprint := "13436916140713291117")
*Theorems: a function reads back.* For every dialect with a
{ref "The-fir-specification--Text-format--Grammar"}[text format], every
function $`f` such that $`\mathrm{tyattr}(t)` is written as a type for
each type $`t` of $`\mathrm{types}(f)`, every word $`k` and every position
$`p`, the reader of an item of kind $`k` at $`p`
{ref "The-fir-specification--Text-format--The-grammar-step"}[reads] the
{ref "The-fir-specification--Text-format--Lexing-printed-text"}[tokens of $`f`]
after its first, the word `func`, as the
{ref "The-fir-specification--Text-format--The-tree-that-the-grammar-reads"}[tree of $`f`]
with the kind $`k`, before any token, up to positions. With $`k` = `func`
it reads them as the tree of $`f`; with $`k` = `extern` it reads the
tokens of an external declaration after its kind, the header of a function
with no blocks, as the declaration's tree.

Here $`\mathrm{types}(f)` is every type that the text of $`f` states: its
result types, and the type of each value it defines, at any depth. The
tokens after `func` are the {ref "The-fir-specification--Text-format--The-parser"}[token]
$`\mathsf{sym}~s`, `(`, the parameters, each followed by its attributes,
and `...` when $`f` is variadic, `)`, then `->` and the result types, each
followed by its attributes, when there are any, then `{`, the blocks and
`}`. At each choice the reader looks at the next token: a `)` after the
`(` means no parameters, and anything else starts them; a `->` starts the
results; and a word after the `{` would start items, but the body of $`f`
starts with a label or is `}`, so it is read as blocks, even when there are
none. The attributes of the last result are read with it, so no attribute
is left for the item, since `{` follows. The tree keeps the attributes of
each parameter and result, and whether the parameters end in `...`.
:::

:::readable Fir.head_attrs Fir.DialectItem.reads (pin := Fir.DialectItem.tokens) (pin := Fir.DialectItem.tree) (pin := Fir.DialectItem.types) (fingerprint := "7481105875845738062")
*Theorems: an item of a dialect's kind reads back.* The tokens of a list
of attributes, then `{`, start with a token that starts an attribute, or
with the `{` when the list is empty. So the reader of an item, after the
parameters and the results, knows where the attributes end.

For every dialect with a
{ref "The-fir-specification--Text-format--Grammar"}[text format], every
item $`i` of a dialect's kind such that $`\mathrm{tyattr}(t)` is written as
a type for each type $`t` of $`\mathrm{types}(i)`, and every position
$`p`, the reader of an item of the kind of $`i` at $`p`
{ref "The-fir-specification--Text-format--The-grammar-step"}[reads] the
tokens of $`i` after its kind as the tree of $`i` before any token, up to
positions: its symbol, `(`, its parameters, `)`, its results after `->`
when it has any, its attributes, one after the other, then `{` and `}`,
its empty body. The reader takes attributes after the last result as that
result's, so the tree of $`i` writes the attributes of $`i` there, and the
proof reads them as if its last result carried them and every other
result none.
:::
