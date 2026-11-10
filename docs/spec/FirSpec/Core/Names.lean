import VersoManual
import Fir.Core.Names
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core's words, which renders
`Fir.Core.Names` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "The core's words are bare: readable blocks" =>

:::moduleDocs (fingerprint := "13044301016779446508")
:::

:::readable Fir.wordDialect_eq_none (fingerprint := "13075370100625360433")
*Theorem: a word with no $`.` names no dialect.* If $`w` holds no $`.`,
then $`\mathrm{dialect}(w) = \bot`.
:::

:::readable Fir.Core.instDialectSet Fir.Core.name_new Fir.Core.opName_bare Fir.Core.opAttrs_bare Fir.Core.tyAttr_bare Fir.Core.lawfulDialectSet Fir.Core.instLawfulDialectSet (fingerprint := "13595859503828867090")
*Theorems: the core's words are bare.* The core dialect's set is empty:
$`\mathrm{names}(\mathrm{core}) = \epsilon`. No name of a core op holds a
$`.`, no word of a core op's attributes does (the flags, the predicates and
the constants $`\texttt{true}` and $`\texttt{false}`), and no core type
does: $`\texttt{ptr}` and $`\texttt{i}N`, whose width is written in
decimal digits. So the core's words name no dialect, and its words stay in
its empty set, and every dialect's name is new to the core.
:::
