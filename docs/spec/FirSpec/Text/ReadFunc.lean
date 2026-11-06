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

:::readable Fir.bind_reads (fingerprint := "11770048284880457070")
*Lemma: proof plumbing for one step followed by another.* Let $`X` be a
step that may fail, and $`K` what runs on its result. If $`X` succeeds with
a result that has a property $`Q`, and $`K` succeeds with a result that
has a property $`P` from every result with $`Q`, then $`X` followed by
$`K` succeeds with a result that has $`P`. The proof below uses it to take
the reader of an item one part at a time.
:::

:::readable Fir.Func.reads (pin := Fir.Text.readItem) (pin := Fir.Func.tokens) (pin := Fir.Func.types) (fingerprint := "10566353448406851408")
*Theorem: a function reads back.* For every dialect with a
{ref "The-fir-specification--Text-format--Grammar"}[text format], every
function $`f` such that $`\mathrm{tyattr}(t)` is written as a type for
each type $`t` of $`\mathrm{types}(f)`, and every position $`p`, the reader
of an item of kind `func` at $`p`
{ref "The-fir-specification--Text-format--The-grammar-step"}[reads] the
{ref "The-fir-specification--Text-format--Lexing-printed-text"}[tokens of $`f`]
after its first, the word `func`, as the
{ref "The-fir-specification--Text-format--The-tree-that-the-grammar-reads"}[tree of $`f`]
before any token, up to positions.

Here $`\mathrm{types}(f)` is every type that the text of $`f` states: its
result types, and the type of each value it defines, at any depth. The
tokens after `func` are $`\mathsf{sym}~s`, `(`, the parameters, `)`, then
`->` and the result types when there are any, then `{`, the blocks and
`}`. At each choice the reader looks at the next token: a value after the
`(` starts parameters and a `)` means none; a `->` starts result types; and
a word after the `{` would start items, but the body of $`f` starts with a
label or is `}`, so it is read as blocks, even when there are none. No
attribute is read, since `{` follows the result types.
:::
