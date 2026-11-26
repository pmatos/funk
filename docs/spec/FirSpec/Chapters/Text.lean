import VersoManual
import Fir
import FirSpecSite.ReadableElab
import FirSpec.ReadableDocs

open Verso.Genre Manual
open FirSpecSite

set_option pp.rawOnError true

/-!
The chapter on the text format of the fir specification, which
`FirSpec.lean` includes after the chapter on traces. It is a document of
its own so that `FirSpec.lean` keeps within the file-size budget
(ADR-2026-10-28-0724). Each section renders one module of `lean/Fir`.
-/

#doc (Manual) "Text format" =>

{includeReadable "." Fir.Text.Lexical "Tokens" FirSpec.Text.Lexical (level := 1)}

{includeReadable "." Fir.Text.Grammar "Grammar" FirSpec.Text.Grammar (level := 1)}

{includeReadable "." Fir.Text.LayoutLaws "The data layout's text, proved" FirSpec.Text.LayoutLaws (level := 1)}

{includeReadable "." Fir.Text.GlobalText "Globals in text" FirSpec.Text.GlobalText (level := 1)}

{includeReadable "." Fir.Text.GlobalLaws "Globals in text, proved" FirSpec.Text.GlobalLaws (level := 1)}

{includeReadable "." Fir.Core.TypeText "The core types in text" FirSpec.Core.TypeText (level := 1)}

{includeReadable "." Fir.Core.Text "The core dialect in text" FirSpec.Core.Text (level := 1)}

{includeReadable "." Fir.Core.AllocaText "Stack allocation in text" FirSpec.Core.AllocaText (level := 1)}

{includeReadable "." Fir.Core.LoadText "Loads in text" FirSpec.Core.LoadText (level := 1)}

{includeReadable "." Fir.Core.StoreText "Stores in text" FirSpec.Core.StoreText (level := 1)}

{includeReadable "." Fir.Core.MemCopyText "Copies and moves in text" FirSpec.Core.MemCopyText (level := 1)}

{includeReadable "." Fir.Core.MemSetText "Fills in text" FirSpec.Core.MemSetText (level := 1)}

{includeReadable "." Fir.Core.PtrIntText "Pointers as integers in text" FirSpec.Core.PtrIntText (level := 1)}

{includeReadable "." Fir.Core.FieldAddrText "Field addresses in text" FirSpec.Core.FieldAddrText (level := 1)}

{includeReadable "." Fir.Core.GlobalAddrText "Addresses of globals in text" FirSpec.Core.GlobalAddrText (level := 1)}

{includeReadable "." Fir.Core.FuncAddrText "Addresses of functions in text" FirSpec.Core.FuncAddrText (level := 1)}

{includeReadable "." Fir.Core.TextSamples "The core dialect's text, checked" FirSpec.Core.TextSamples (level := 1)}

{includeReadable "." Fir.Core.FloatText "Float constants in text" FirSpec.Core.FloatText (level := 1)}

{includeReadable "." Fir.Core.RoundingText "The rounding mode in text" FirSpec.Core.RoundingText (level := 1)}

{includeReadable "." Fir.Core.FloatOpText "Float arithmetic in text" FirSpec.Core.FloatOpText (level := 1)}

{includeReadable "." Fir.Text.Print "The canonical printer" FirSpec.Text.Print (level := 1)}

{includeReadable "." Fir.Text.SigAttrs "The attributes of a signature" FirSpec.Text.SigAttrs (level := 1)}

{includeReadable "." Fir.Text.RoundTrip "Round trips" FirSpec.Text.RoundTrip (level := 1)}

{includeReadable "." Fir.Core.TypeTextLaws "The core types in text are lawful" FirSpec.Core.TypeTextLaws (level := 1)}

{includeReadable "." Fir.Core.AllocaTextLaws "Stack allocation reads back" FirSpec.Core.AllocaTextLaws (level := 1)}

{includeReadable "." Fir.Core.LoadTextLaws "Loads read back" FirSpec.Core.LoadTextLaws (level := 1)}

{includeReadable "." Fir.Core.StoreTextLaws "Stores read back" FirSpec.Core.StoreTextLaws (level := 1)}

{includeReadable "." Fir.Core.MemCopyTextLaws "Copies and moves read back" FirSpec.Core.MemCopyTextLaws (level := 1)}

{includeReadable "." Fir.Core.MemSetTextLaws "Fills read back" FirSpec.Core.MemSetTextLaws (level := 1)}

{includeReadable "." Fir.Core.FloatOpTextLaws "The float ops read back" FirSpec.Core.FloatOpTextLaws (level := 1)}

{includeReadable "." Fir.Core.TextLaws "The core dialect's text is lawful" FirSpec.Core.TextLaws (level := 1)}

{includeReadable "." Fir.Core.FloatTextLaws "Float constants read back" FirSpec.Core.FloatTextLaws (level := 1)}

{includeReadable "." Fir.Text.Lex "The parser" FirSpec.Text.Lex (level := 1)}

{includeReadable "." Fir.Text.Read "Reading the grammar" FirSpec.Text.Read (level := 1)}

{includeReadable "." Fir.Text.ReadLocs "Reading the location table and the module" FirSpec.Text.ReadLocs (level := 1)}

{includeReadable "." Fir.Text.Decode "Decoding" FirSpec.Text.Decode (level := 1)}

{includeReadable "." Fir.Text.Example "Example" FirSpec.Text.Example (level := 1)}

{includeReadable "." Fir.Text.Tokens "Lexing printed text" FirSpec.Text.Tokens (level := 1)}

{includeReadable "." Fir.Text.LexNumbers "Digits and their values" FirSpec.Text.LexNumbers (level := 1)}

{includeReadable "." Fir.Text.LexTokens "Maximal munch" FirSpec.Text.LexTokens (level := 1)}

{includeReadable "." Fir.Text.LexStrings "Escapes and quoted symbols" FirSpec.Text.LexStrings (level := 1)}

{includeReadable "." Fir.Text.LexFloats "Reading printed float literals" FirSpec.Text.LexFloats (level := 1)}

{includeReadable "." Fir.Text.LexLayout "Spaces, line feeds and lists" FirSpec.Text.LexLayout (level := 1)}

{includeReadable "." Fir.Text.LexPrint "Attributes, locations and names" FirSpec.Text.LexPrint (level := 1)}

{includeReadable "." Fir.Text.LexWritable "Tokens that can be written" FirSpec.Text.LexWritable (level := 1)}

{includeReadable "." Fir.Text.LexFunc "A function's signature lexed" FirSpec.Text.LexFunc (level := 1)}

{includeReadable "." Fir.Text.LexModule "Ops, functions and the module" FirSpec.Text.LexModule (level := 1)}

{includeReadable "." Fir.Text.LexWellFormed "Writable tokens" FirSpec.Text.LexWellFormed (level := 1)}

{includeReadable "." Fir.Text.Tree "The tree that the grammar reads" FirSpec.Text.Tree (level := 1)}

{includeReadable "." Fir.Text.ReadAttrs "The grammar step" FirSpec.Text.ReadAttrs (level := 1)}

{includeReadable "." Fir.Text.ReadDefs "Definitions and successors read back" FirSpec.Text.ReadDefs (level := 1)}

{includeReadable "." Fir.Text.ReadParams "Parameters and results read back" FirSpec.Text.ReadParams (level := 1)}

{includeReadable "." Fir.Text.ReadOps "Ops read back" FirSpec.Text.ReadOps (level := 1)}

{includeReadable "." Fir.Text.ReadBlocks "Blocks and regions read back" FirSpec.Text.ReadBlocks (level := 1)}

{includeReadable "." Fir.Text.ReadFunc "A function read back" FirSpec.Text.ReadFunc (level := 1)}

{includeReadable "." Fir.Text.ReadTable "The location table read back" FirSpec.Text.ReadTable (level := 1)}

{includeReadable "." Fir.Text.ReadModule "The module read back" FirSpec.Text.ReadModule (level := 1)}

{includeReadable "." Fir.Text.DecodeScope "The decoding step" FirSpec.Text.DecodeScope (level := 1)}

{includeReadable "." Fir.Text.DecodeBlocks "Blocks and ops decoded back" FirSpec.Text.DecodeBlocks (level := 1)}

{includeReadable "." Fir.Text.DecodeFuncItem "A function's item and an external declaration decoded back" FirSpec.Text.DecodeFuncItem (level := 1)}

{includeReadable "." Fir.Text.DecodeModule "The module decoded back" FirSpec.Text.DecodeModule (level := 1)}

{includeReadable "." Fir.Text.PrintParse "The round trip, proved" FirSpec.Text.PrintParse (level := 1)}

{includeReadable "." Fir.Text.LexAccepted "What the lexer accepts" FirSpec.Text.LexAccepted (level := 1)}

{includeReadable "." Fir.Text.ReadAccepted "What the grammar accepts" FirSpec.Text.ReadAccepted (level := 1)}

{includeReadable "." Fir.Text.ReadAcceptedBlocks "Accepted ops, blocks and regions" FirSpec.Text.ReadAcceptedBlocks (level := 1)}

{includeReadable "." Fir.Text.ReadAcceptedItems "Accepted items" FirSpec.Text.ReadAcceptedItems (level := 1)}

{includeReadable "." Fir.Text.ReadAcceptedModule "An accepted location table" FirSpec.Text.ReadAcceptedModule (level := 1)}

{includeReadable "." Fir.Text.DecodeAcceptedScope "What the first pass accepts" FirSpec.Text.DecodeAcceptedScope (level := 1)}

{includeReadable "." Fir.Text.DecodeAccepted "What the second pass accepts" FirSpec.Text.DecodeAccepted (level := 1)}

{includeReadable "." Fir.Text.DecodeAcceptedFunc "A function and an external declaration as decoded" FirSpec.Text.DecodeAcceptedFunc (level := 1)}

{includeReadable "." Fir.Text.DecodeAcceptedModule "What decoding accepts" FirSpec.Text.DecodeAcceptedModule (level := 1)}

{includeReadable "." Fir.Text.ParseWellFormed "Parsed modules are well formed" FirSpec.Text.ParseWellFormed (level := 1)}
