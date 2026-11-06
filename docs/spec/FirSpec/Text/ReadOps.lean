import VersoManual
import Fir.Text.ReadOps
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on ops read back, which renders
`Fir.Text.ReadOps` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Ops read back: readable blocks" =>

:::readable Fir.lhs_tokens Fir.rhs_tokens (fingerprint := "3167030283771324845")
*Lemmas: proof plumbing.* The
{ref "The-fir-specification--Text-format--Lexing-printed-text"}[tokens of an op]
test whether its results, and its operands and successors, are empty;
these lemmas restate the two tests in the form the proofs below use. The
second also notes that joining an empty list with commas adds nothing.
:::

:::readable Fir.head_uses Fir.head_regions (pin := Fir.Succ.tokens) (pin := Fir.Region.tokensList) (fingerprint := "18439506708691666140")
*Lemmas: what follows an op's attributes starts no attribute, and what
follows its uses ends them.* For every dialect
with a {ref "The-fir-specification--Text-format--Grammar"}[text format]:

* the first token after an op's attributes, which is its first operand,
  its first successor, `{` for its first region, or its location
  reference, starts no attribute and is not `(`;
* the first token after an op's operands and successors, `{` or its
  location reference,
  {ref "The-fir-specification--Text-format--Definitions-and-successors-read-back"}[ends its uses].

So each reader of the op stops where the next one starts.
:::

:::readable Fir.EndsOps (fingerprint := "11884796603434483477")
*Definition: what follows the ops of a block.* A token _ends a block's
ops_ when it is `}`, which ends a region or a function, or a label, which
starts the next block. Neither starts an op.
:::

:::readable Fir.Operation.tokensAfterName Fir.Operation.treeWith (pin := Fir.DialectText) (pin := Fir.Region.tokensList) (pin := Fir.Succ.tokens) (fingerprint := "7109299546903148067")
*Definitions: an op's tokens after its name, and its tree with given
results and name.* For an op $`o` with the op instance $`\iota`, its tokens
after its name are, in order:

* the tokens of its attributes, $`\mathrm{opattrs}(\iota)`;
* the tokens of its operands and successors, separated by commas;
* the tokens of its regions, and the
  {ref "The-fir-specification--Text-format--The-parser"}[token]
  $`\mathsf{locref}~r` for its location reference $`r`.

The tree of $`o` with the results $`d^*` and the name $`w` is the
{ref "The-fir-specification--Text-format--The-tree-that-the-grammar-reads"}[tree of $`o`]
with $`d^*` as its results and $`w` as its name. The reader of an op takes
the results and the name that it has already read, so the lemmas below
state what it gives in these terms.
:::

:::readable Fir.Operation.tokens_eq (pin := Fir.Operation.tokens) (fingerprint := "4503156691049850776")
*Theorem: an op's tokens are its results, its name, then the rest.* For
every dialect with a
text format and every op $`o` with the op instance $`\iota`, the tokens of $`o`
are the tokens of its results followed by `=`, when it has results, then
$`\mathsf{word}~\mathrm{opname}(\iota)`, then its tokens after its name.
:::

:::readable Fir.readOpBody_reads (pin := Fir.Text.readOpBody) (fingerprint := "17585542946757790440")
*Theorem: the rest of an op reads back.* For every dialect with a text
format and every op $`o`, suppose that the reader of regions reads the
tokens of the regions of $`o` as their trees before any location reference,
up to positions. Then, for all results $`d^*` as written, every name $`w`
and every position $`p`, the reader of the rest of an op with the results
$`d^*` and the name $`w` at $`p`
{ref "The-fir-specification--Text-format--The-grammar-step"}[reads] the
tokens of $`o` after its name as the tree of $`o` with the results
$`\mathrm{erase}(d^*)` and the name $`w`, before any token, up to
positions.

It reads the attributes, then the operands and successors, then the
regions, then the location reference, each stopped by the first token of
the next.
:::

:::readable Fir.readOpWithResults_reads (pin := Fir.Text.readOpWithResults) (pin := Fir.defTokens) (fingerprint := "12844763735832856473")
*Theorem: an op with results reads back after its first value.* For every
dialect with a text format, every op $`o`, definitions
$`x_1 : T_1, \dots, x_n : T_n` with $`n \geq 1` such that each
$`\mathrm{tyattr}(T_i)` is written as a type, and every name $`w`: suppose
that, for all results as written and every position, the reader of the rest
of an op reads the tokens of $`o` after its name as in the theorem above.
Then, for every position $`p`, the reader of an op whose first result is
$`x_1` at $`p` reads

$$`\begin{aligned} & \texttt{:}~\mathrm{tokens}(\mathrm{tyattr}(T_1)) \\ & \texttt{,}~\mathrm{tokens}(x_2 : T_2)~\dots~\texttt{,}~\mathrm{tokens}(x_n : T_n) \\ & \texttt{=}~\mathsf{word}~w~\mathit{after} \end{aligned}`

as the tree of $`o` with the trees of $`x_1 : T_1, \dots, x_n : T_n` as
its results and $`w` as its name, before any token, up to positions. Here
$`\mathit{after}` is the tokens of $`o` after its name. The reader of ops
has already taken $`\mathsf{value}~x_1`, which tells it that an op with
results starts.
:::

:::readable Fir.readOps_nil_reads Fir.readOps_cons_reads (pin := Fir.Text.readOps) (pin := Fir.Operation.tokensList) (fingerprint := "14391684728431522413")
*Theorems: ops read back, one at a time.* For every dialect with a text
format, the reader of ops reads tokens of ops as their trees before any
token that ends a block's ops, up to positions:

* for no ops: it reads nothing;
* for an op $`o` followed by ops $`o^*`: it reads them when the type of
  each result of $`o` is written as a type, the reader of the rest of an op reads the
  tokens of $`o` after its name as the theorem above says, for all results,
  names and positions, and the reader of ops reads the tokens of $`o^*` as
  their trees before a token that ends a block's ops.

An op starts with $`\mathsf{value}~x` when it has results and with its
name otherwise, and the reader of ops takes the matching branch.
:::
