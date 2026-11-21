import VersoManual
import Fir.Text.ReadParams
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a signature's parameters and results read back, which renders
`Fir.Text.ReadParams` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Parameters and results read back: readable blocks" =>

:::moduleDocs (fingerprint := "11435999027542391800")
:::

:::readable Fir.Text.eraseParam Fir.Text.paramTree Fir.Text.paramToks (fingerprint := "8907896217843250291")
*Definitions: a parameter as read, as its tree and as tokens.* A parameter
as the reader keeps it is a definition, with its positions, and its
attributes, each with its position; without positions it is the
definition's tree and the attributes. A parameter of a function, a
definition $`x` and attributes $`A`, has the tree of $`x` and $`A`, and
the tokens of $`x` followed by those of each attribute of $`A`.
:::

:::readable Fir.Text.attrs_head Fir.Text.attrs_head_ne (fingerprint := "5738215031612243121")
*Lemmas: attributes start with an attribute's token.* For every list of
attributes, the first of their tokens, if any, starts an attribute, and so
is not `(`. So a reader of attributes after a definition or a type knows
where they start, and where they end: at the first token that starts none.
:::

:::readable Fir.Text.readParam_reads (pin := Fir.Text.readParam) (fingerprint := "18138506252370753172")
*Theorem: a parameter reads back.* For every dialect with a
{ref "The-fir-specification--Text-format--Grammar"}[text format] and every
parameter, a definition $`x` whose type is written as a type and
attributes $`A`, the reader of a parameter
{ref "The-fir-specification--Text-format--The-grammar-step"}[reads] its
tokens as its tree and $`A`, up to positions, before any token that starts
no attribute and is not `(`.
:::

:::readable Fir.Text.ellipsisToks Fir.Text.readMoreParams_reads (pin := Fir.Text.readMoreParams) (fingerprint := "9987731701386021766")
*Definition and theorem: further parameters read back.* The tokens of an
ending in `...` are `...` when no parameter comes before, `, ...` when one
does, and nothing when the parameters do not end in it. For every dialect
with a text format, every list of parameters each of whose types is
written as a type, and every $`v`, the reader of further parameters reads
`, ` and each parameter's tokens, for each parameter, then the ending of
$`v` after a parameter, as the parameters' trees and whether they end in
`...`, before `)`.
:::

:::readable Fir.Text.paramsToks Fir.Text.readParams_reads (pin := Fir.Text.readParams) (fingerprint := "9705388915140983730")
*Definition and theorem: an item's parameters read back.* The tokens of
parameters $`p_1, \dots, p_n` that may end in `...` are those of each
$`p_i`, separated by commas, then the ending. For every dialect with a text
format, and every list of parameters each of whose types is written as a
type that is not empty or ends in `...`, the reader of an item's
parameters reads their tokens as their trees and whether they end in
`...`, before `)`. A list that is empty and does not end in `...` has no
tokens, and the reader of an item does not call this reader on it: it sees
the `)` first.
:::

:::readable Fir.Text.eraseResult Fir.Text.resultToks Fir.Text.readResult_reads (pin := Fir.Text.readResult) (fingerprint := "18064222257306033632")
*Definitions and theorem: a result reads back.* A result as read, without
positions, is its type, with a position, and its attributes; its tokens
are the type's, then the attributes'. For every dialect with a text format
and every result whose type is written as a type, the reader of a result
reads its tokens as its type and its attributes, up to positions, before
any token that starts no attribute and is not `(`.
:::

:::readable Fir.Text.lastAttrs Fir.Text.lastAttrs_fst Fir.Text.lastAttrs_dropLast Fir.Text.lastAttrs_getLast Fir.Text.lastAttrs_tokens (fingerprint := "13422101506870577081")
*Definition and lemmas: an item's attributes after its last result.* An
item of a dialect's kind writes its attributes $`A` after its results, and
the grammar reads them as the last result's. $`\mathrm{last}(xs, A)` pairs
each of $`xs` with no attributes, but the last, which it pairs with $`A`.
Its first parts are $`xs`; its parts but the last carry no attributes; the
last, when $`xs` is not empty, carries $`A`; and the tokens of $`xs`,
separated by commas, then those of $`A`, are the tokens of the pairs of
$`\mathrm{last}(xs, A)`, each followed by its attributes, separated by
commas.
:::

:::readable Fir.Text.map_eraseAt Fir.Text.params_read Fir.Text.results_read (fingerprint := "724236599342218090")
*Lemmas: what parameters and results read back hold.* Erasing the positions
of attributes gives their tree. Parameters read back as the trees of
parameters hold, without positions, their definitions' trees and their
attributes. Results read back as the trees of results hold their types,
the attributes of each result but the last, and the attributes of the
last, or none when there are no results.
:::
