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

:::moduleDocs (fingerprint := "9280140473958763558")
:::

:::readable Fir.InitPiece.attr Fir.Global.attrs Fir.Global.item (fingerprint := "725683294286962110")
*Definition: how a global is written.* A global $`G` is written as an item
of the core's kind `data` with the generic production of an item, with no
parameters, no results and an empty body (ADR-2026-11-19-0124). Its
attributes are, in order: `memory(n)` when its memory $`n` is not 0, then
`size(z)` and `align(a)`, then the word `constant` when $`G` is constant
and the word `export` when it is exported, then one attribute for each
piece of its initializer: `units(u, ...)` for $`\mathsf{units}~u^*`,
`zeros(n)` for $`\mathsf{zeros}~n`, `addr(@s)` for
$`\mathsf{addr}~s~0` and `addr(@s, k)` for $`\mathsf{addr}~s~k` with
$`k \neq 0`. For example
`data @msg() size(8) align(1) constant units(104, 105, 0) {` and `}`.
The words `data` and `constant` are the agent's choice in place of
ADR-2026-11-09-1546's `global` and `const`, which the core's text already
writes, so that the G0 check keeps generic code free of the core's words.
:::

:::readable Fir.InitPiece.decodeUnit Fir.InitPiece.decode (fingerprint := "8038383235798892266")
*Definition: reading a piece.* A unit of `units(...)` is any integer that
is not negative. `zeros(n)` reads when $`n` is within the limit
$`2^{64} - 1`; `addr(@s)` reads as the address of $`s` plus 0, and
`addr(@s, k)` when $`k` is within the limit and not 0. Every other
attribute is no piece.
:::

:::readable Fir.GlobalFault Fir.Global.noMemory Fir.Global.decodeMem Fir.Global.decodeFlag Fir.Global.decodePieces Fir.Global.decodeAttrs (fingerprint := "18408558030186929670")
*Definition: reading a global.* Reading a global's attributes either gives
the global or stops at a fault: the index of the attribute that does not
read, or none when there are too few, and why. A first attribute
`memory(...)` must be `memory(n)` with $`1 \le n \le 2^{64} - 1`; any
other first attribute leaves the memory 0. Then come `size(z)` and
`align(a)`, each within the limit; then the word `constant`, if it comes,
and the word `export`, if it comes; then pieces up to the end, each of
which must read, or the first that does not is the fault. So each global
has one spelling: `memory(0)`, the flags in the other order, a flag after
a piece and `addr(@s, 0)` do not read.
:::
