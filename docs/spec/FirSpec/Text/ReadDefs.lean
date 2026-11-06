import VersoManual
import Fir.Text.ReadDefs
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on definitions and successors read
back, which renders `Fir.Text.ReadDefs` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Definitions and successors read back: readable blocks" =>

:::readable Fir.Text.readDefType_reads (pin := Fir.Text.readDefType) (pin := Fir.Attr.IsType) (fingerprint := "9902619171847891488")
*Theorem: the type of a definition reads back.* For every dialect with a
{ref "The-fir-specification--Text-format--Grammar"}[text format], every
position $`p` and every definition $`x : T` such that
$`\mathrm{tyattr}(T)` is written as a type, the reader of the type of a
definition of $`x` at $`p`
{ref "The-fir-specification--Text-format--The-grammar-step"}[reads]
$`\texttt{:}~\mathrm{tokens}(\mathrm{tyattr}(T))` as the
{ref "The-fir-specification--Text-format--The-tree-that-the-grammar-reads"}[tree]
of $`x : T` before any token but `(`, up to positions.
:::

:::readable Fir.Text.readDef_reads (pin := Fir.Text.readDef) (pin := Fir.defTokens) (fingerprint := "4813841091690282429")
*Theorem: a definition reads back.* For every dialect with a text format
and every definition $`x : T` such that $`\mathrm{tyattr}(T)` is written as
a type, the reader of a definition reads its tokens,
$`\mathsf{value}~x~\texttt{:}~\mathrm{tokens}(\mathrm{tyattr}(T))`, as the
tree of $`x : T` before any token but `(`, up to positions. A `(` after the
type would apply a type that is a word.
:::

:::readable Fir.Text.flatMap_comma_map (fingerprint := "524672996597415394")
*Lemma: proof plumbing.* Two ways of writing a comma before the tokens of
each element of a list give the same tokens.
:::

:::readable Fir.Text.readDefs_reads (pin := Fir.Text.readDefs) (pin := Fir.defsTokens) (fingerprint := "9624342035208024670")
*Theorem: a list of definitions reads back.* For every dialect with a text
format and every list of one or more definitions $`x_i : T_i` such that
each $`\mathrm{tyattr}(T_i)` is written as a type, the reader of
definitions reads their tokens, separated by commas, as their trees before
any token but `(` and a comma, up to positions. A comma after the list
would continue it.
:::

:::readable Fir.Text.readSuccArgs_reads (pin := Fir.Text.readSuccArgs) (fingerprint := "12532690489152718995")
*Theorem: the values that a successor passes read back.* For every list of
one or more values $`a_1, \dots, a_n`, the reader of a successor's
arguments reads
$`\mathsf{value}~a_1~\texttt{,}~\dots~\texttt{,}~\mathsf{value}~a_n~\texttt{)}`
as $`a_1, \dots, a_n`, before any token.
:::

:::readable Fir.Text.Succ.reads (pin := Fir.Text.readSucc) (pin := Fir.Succ.tokens) (fingerprint := "17433520648719123204")
*Theorem: a successor reads back.* For every
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[successor]
$`s`, the reader of a successor reads the tokens of $`s` as $`s` before
any token but `(`: its label, then, when it passes values, `(`, the values
separated by commas, and `)`. A `(` after a successor that passes nothing
would be read as its arguments.
:::

:::readable Fir.Text.EndsUses Fir.Text.EndsUses.ne (fingerprint := "2340308083200363600")
*Definition and lemma: what follows an op's operands and successors.* A
token _ends an op's uses_ when it is `{`, which starts a region, or a
location reference, which ends the op. No such token is a comma or `(`.
:::

:::readable Fir.Text.readMore_succs (pin := Fir.Text.readMore) (fingerprint := "17245772931178089068")
*Theorem: the successors after the first read back.* For every list of
successors $`s_1, \dots, s_n`, the reader of the rest of a list of
successors reads
$`\texttt{,}~\mathrm{tokens}(s_1)~\dots~\texttt{,}~\mathrm{tokens}(s_n)`
as $`s_1, \dots, s_n` before any token that ends an op's uses.
:::

:::readable Fir.Text.readMoreOperands_reads (pin := Fir.Text.readMoreOperands) (fingerprint := "11514527456933062452")
*Theorem: the operands after the first, and the successors, read back.*
For every list of values $`v_1, \dots, v_m` and every list of successors
$`s_1, \dots, s_n`, the reader of the operands after the first reads

$$`\begin{aligned} & \texttt{,}~\mathsf{value}~v_1~\dots~\texttt{,}~\mathsf{value}~v_m \\ & \texttt{,}~\mathrm{tokens}(s_1)~\dots~\texttt{,}~\mathrm{tokens}(s_n) \end{aligned}`

as the operands $`v_1, \dots, v_m`, each at the empty position $`p_0`,
and the successors $`s_1, \dots, s_n`, before any token that ends an op's
uses, up to the operands' positions.
:::

:::readable Fir.Text.readOperands_reads (pin := Fir.Text.readOperands) (fingerprint := "4332270993736212724")
*Theorem: an op's operands and successors read back.* For every list of
values $`v_1, \dots, v_m` and every list of successors $`s_1, \dots, s_n`,
the reader of an op's operands and successors reads the tokens of the
operands, $`\mathsf{value}~v_i`, then those of the successors,
$`\mathrm{tokens}(s_j)`, all separated by commas, as the operands, each at
$`p_0`, and the successors, before any token that ends an op's uses, up to
the operands' positions. Either list may be empty, and so may both.
:::

:::readable Fir.Text.readOpLoc_reads (pin := Fir.Text.readOpLoc) (fingerprint := "4487361778260717652")
*Theorem: an op's location reference reads back.* For every location
reference $`r`, the reader of an op's location reference reads
$`\mathsf{locref}~r` as $`r`, before any token. It reads one token, so
nothing that follows can change what it reads.
:::
