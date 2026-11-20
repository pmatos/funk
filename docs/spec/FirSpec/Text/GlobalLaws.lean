import VersoManual
import Fir.Text.GlobalLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on globals in text, proved, which renders
`Fir.Text.GlobalLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Globals in text, proved: readable blocks" =>

:::moduleDocs (fingerprint := "13668561535012406255")
:::

:::readable Fir.InitPiece.units_writable Fir.InitPiece.attr_writable Fir.Global.attr_writable (fingerprint := "14020469643648516491")
*Theorems: a global can be written.* Every attribute that a global
writes can be written as a token, whatever its numbers and symbols: its
heads and flags are words, and its numbers and symbols are tokens.
:::

:::readable Fir.InitPiece.decodeUnits_map Fir.InitPiece.decode_units Fir.InitPiece.decode_zeros Fir.InitPiece.decode_addr_zero Fir.InitPiece.decode_addr_succ Fir.InitPiece.decode_attr (fingerprint := "12914959394152308883")
*Theorem: a piece reads back.* For every piece $`p` whose numbers are
within the limit, reading what $`p` writes gives $`p` back:

$$`\mathrm{decode}(\mathrm{attr}(p)) = p`
:::

:::readable Fir.InitPiece.inLimits_of_decode Fir.InitPiece.mapM_decode_attr Fir.InitPiece.inLimits_of_mapM_decode Fir.Global.decodePieces_map Fir.Global.inLimits_of_decodePieces (fingerprint := "16099851658615523558")
*Theorems: pieces read back, within the limit.* A piece that reads has its
numbers within the limit. The pieces that a global writes read back, from
any index, when their numbers are within the limit, and pieces that read
have their numbers within the limit.
:::

:::readable Fir.Global.decodeFlag_const Fir.Global.decodeFlag_export Fir.InitPiece.map_attr_head Fir.Global.decodeMem_size Fir.Global.decodeMem_memory (fingerprint := "5446604386067953319")
*Theorems: the header reads back.* The flag `constant` reads back as
written when what follows starts with no such word, and so does `export`;
what pieces write starts with no word. A global of memory 0 writes no
memory and reads as one, and a global of any other memory within the limit
reads its `memory(n)` back.
:::

:::readable Fir.Global.decodeAttrs_attrs Fir.Global.inLimits_of_decodeAttrs Fir.Global.name_of_decodeAttrs (fingerprint := "7885585374381852042")
*Theorems: a global has one spelling.* For every global $`G` whose numbers
are within the limit, reading the attributes $`G` writes, with its symbol,
gives $`G` back:

$$`\mathrm{decodeAttrs}(\mathrm{sym}(G), \mathrm{attrs}(G)) = G`

And a global that reads from attributes has its numbers within the limit
and the symbol it was read with.
:::
