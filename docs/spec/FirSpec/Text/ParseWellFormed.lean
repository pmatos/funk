import VersoManual
import Fir.Text.ParseWellFormed
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on parsed modules being well formed,
which renders `Fir.Text.ParseWellFormed` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Parsed modules are well formed: readable blocks" =>

:::moduleDocs (fingerprint := "717121213209667201")
:::

:::readable Fir.parse_wellFormed (pin := Fir.parse) (pin := Fir.Module.WellFormed) (fingerprint := "3712612152196595362")
*Theorem: every module that the parser gives is well formed.* Let $`d` be
a dialect with a signature, validation rules and a text, whose text is
{ref "The-fir-specification--Text-format--Grammar"}[lawful]. For every
text $`t` and every module $`m` of $`d`: when the
{ref "The-fir-specification--Text-format--Decoding"}[parser] reads $`t`
as $`m`, $`m` is
{ref "The-fir-specification--Text-format--Round-trips"}[well formed]:

$$`\mathrm{parse}(t) = \mathsf{ok}(m) \implies m \text{ is well formed}`

Here $`\mathrm{parse}(t) = \mathsf{ok}(m)` says that the parser reads $`t`
without an error, and gives $`m`. The parser lexes $`t`, reads the tokens
by the grammar, and decodes the module as read; the proof chains the three
steps. The
{ref "The-fir-specification--Text-format--What-the-lexer-accepts"}[lexer's step]
gives tokens that can be written, the
{ref "The-fir-specification--Text-format--An-accepted-location-table"}[grammar step]
turns them into a module as read that can be written, and the
{ref "The-fir-specification--Text-format--What-decoding-accepts"}[decoding step]
turns that into a well-formed module.

It holds for every text that the parser accepts, not only for the texts
that the printer writes: one with comments, other spacing, no final line
feed, or written by another tool.
:::

:::readable Fir.parse_print_of_parse (pin := Fir.parse) (fingerprint := "395908951375606997")
*Theorem: the printed form of a parsed module reads back as it.* Let $`d`
be a dialect with a signature, validation rules and a text, whose text is
lawful. For every text $`t` and every module $`m` of $`d`: when the parser
reads $`t` as $`m`, it reads the
{ref "The-fir-specification--Text-format--The-canonical-printer"}[printed form]
of $`m` as $`m` again:

$$`\begin{aligned} & \mathrm{parse}(t) = \mathsf{ok}(m) \\ & \quad \implies \mathrm{parse}(\mathrm{print}(m)) = \mathsf{ok}(m) \end{aligned}`

Here $`\mathrm{print}(m)` is the canonical text of $`m`. It follows from
the previous theorem and the
{ref "The-fir-specification--Text-format--The-round-trip___-proved"}[round trip],
which reads back the printed form of every well-formed module. So
formatting a text, parsing it and printing the result, is idempotent on
every text that the parser accepts: formatting the formatted text again
gives the same text.
:::

:::readable Fir.Core.parse_wellFormed Fir.Core.parse_print_of_parse (pin := Fir.parse) (fingerprint := "14661911985588144897")
*Theorems: the same for the core dialect.* For every text $`t` and every
module $`m` of the core dialect, when the parser reads $`t` as $`m`:

* $`m` is well formed;
* the parser reads the printed form of $`m` as $`m`.

The core dialect's text is
{ref "The-fir-specification--Text-format--The-core-dialect___s-text-is-lawful"}[lawful],
so both theorems above apply to it.
:::
