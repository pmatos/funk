import VersoManual
import Fir.Text.LexFunc
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a function's signature lexed, which renders
`Fir.Text.LexFunc` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "A function's signature lexed: readable blocks" =>

:::moduleDocs (fingerprint := "16746834050724247943")
:::

:::readable Fir.spells_withAttrs Fir.spells_ellipsis (pin := Fir.printAttrs) (fingerprint := "3596748929222349642")
*Lemmas: a definition or a type with its attributes, and `...`, lex
back.* For every text $`s` that lexes to tokens $`t` and every list of
attributes whose tokens can be written, $`s` followed by each attribute
after a space lexes to $`t` followed by the attributes' tokens: an
attribute starts after a space, so $`s` ends where it would end alone. And
the text `...` lexes to the one token $`\texttt{...}`.
:::

:::readable Fir.Func.spellsParams Fir.Func.spellsResults (pin := Fir.Func.printParams) (pin := Fir.Func.printResults) (pin := Fir.Func.paramsTokens) (pin := Fir.Func.resultsTokens) (pin := Fir.Func.paramAttrsAll) (pin := Fir.Func.resultAttrsAll) (fingerprint := "15721662831336692504")
*Theorems: a function's parameters and results lex back.* For every
dialect with a {ref "The-fir-specification--Text-format--Grammar"}[text format]
and every function $`f` whose parameters' tokens can be written, the
printed parameters of $`f` lex to their tokens: each definition followed by
its attributes, separated by commas, then `...` when $`f` is variadic,
after `, ` when a parameter comes before. In the same way, when the tokens
of the results of $`f` can be written, its printed results lex to their
tokens: nothing when $`f` returns nothing, and otherwise ` -> ` and each
result type followed by its attributes, separated by commas.
:::
