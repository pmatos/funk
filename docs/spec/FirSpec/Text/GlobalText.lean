import VersoManual
import Fir.Text.GlobalText
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on globals in text, which renders
`Fir.Text.GlobalText` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Globals in text: readable blocks" =>

:::moduleDocs (fingerprint := "9343948432328461853")
:::

:::readable Fir.InitPiece.attr Fir.Global.attrs Fir.Global.item (fingerprint := "3835029162633092479")
*Definition: how a global is written.* A global $`G` is written as an item
of the core's kind `global` with the generic production of an item, with no
parameters, no results and an empty body (ADR-2026-11-19-0124). Its
attributes are, in order: `memory(n)` when its memory $`n` is not 0, then
`size(z)` and `align(a)`, then the word `const` when $`G` is constant
and the word `export` when it is exported, then one attribute for each
piece of its initializer: `units(u, ...)` for $`\mathsf{units}~u^*`,
`zeros(n)` for $`\mathsf{zeros}~n`, `addr(@s)` for
$`\mathsf{addr}~s~0` and `addr(@s, k)` for $`\mathsf{addr}~s~k` with
$`k \neq 0`. For example
`global @msg() size(8) align(1) const units(104, 105, 0) {` and `}`.
The words `global` and `const` are ADR-2026-11-09-1546's, as the human
ruled on 2026-11-20 (#237 Q4). The core's text writes them too, as
`alloca`'s kind and as an op, so the G0 check lists them among the words
that generic code shares with the core.
:::

:::readable Fir.InitPiece.decodeUnit Fir.InitPiece.decode (fingerprint := "14251321511947220698")
*Definition: reading a piece.* A unit of `units(...)` is any integer that
is not negative. `zeros(n)` reads when $`n` is within the limit
$`2^{64} - 1`; `addr(@s)` reads as the address of $`s` plus 0, and
`addr(@s, k)` when $`k` is within the limit and not 0. Every other
attribute is no piece.
:::

:::readable Fir.GlobalFault Fir.Global.noMemory Fir.Global.decodeMem Fir.Global.decodeFlag Fir.Global.decodePieces Fir.Global.decodeAttrs (fingerprint := "5505819918022884100")
*Definition: reading a global.* Reading a global's attributes either gives
the global or stops at a fault: the index of the attribute that does not
read, or none when there are too few, and why. A first attribute
`memory(...)` must be `memory(n)` with $`1 \le n \le 2^{64} - 1`; any
other first attribute leaves the memory 0. Then come `size(z)` and
`align(a)`, each within the limit; then the word `const`, if it comes,
and the word `export`, if it comes; then pieces up to the end, each of
which must read, or the first that does not is the fault. So each global
has one spelling: `memory(0)`, the flags in the other order, a flag after
a piece and `addr(@s, 0)` do not read.
:::
