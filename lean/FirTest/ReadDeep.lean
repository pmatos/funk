import Fir
import FirRef.Utf8

/-!
Tests of the lexer and the readers that `fir-ref` runs: `FirRef.parse`
reads a text with `FirRef.readText`, which lexes over the text's positions
and reads with loops that take no stack per level of nesting. This module
imports `FirRef.Utf8`, as `fir-ref` does, so `Fir.parse` below runs as
`FirRef.parse`.

The checks parse texts nested 100,000 levels deep in regions, items and
attributes, and a block of 100,000 ops, and get the decoder's verdict on
each: the reader reads them whole. A lexer error at the end of a text is
reported before a reader error at its start, as the spec reports it. On
small texts, `readText` gives what the spec's lexer and `Text.readModule`
give, errors included. The last checks pin the axioms of the theorems to
Lean's standard ones.
-/

namespace FirTest

open Fir Fir.Text

/-- The location table that every text below ends with. -/
def locsText : String := "\nlocs {\n  @0 = unknown\n}\n"

/-- A function whose block nests `n` ops in regions, with the undefined
value `%x` innermost. -/
def deepRegionsText (n : Nat) : String :=
  "func @f() {\n^e:\n" ++ String.join (List.replicate n "br {\n^b:\n") ++ "ret %x @0\n" ++
    String.join (List.replicate n "} @0\n") ++ "}\n" ++ locsText

/-- `n` functions, each in the body of the one before. -/
def deepItemsText (n : Nat) : String :=
  String.join (List.replicate n "func @a() {\n") ++ String.join (List.replicate n "}\n") ++ locsText

/-- An op whose attribute is applied `n` levels deep. -/
def deepAttrText (n : Nat) : String :=
  "func @f() {\n^e:\n  ret " ++ String.join (List.replicate n "h(") ++ "x" ++
    String.join (List.replicate n ")") ++ " @0\n}\n" ++ locsText

/-- A block of `n` constants. -/
def flatOpsText (n : Nat) : String :=
  "func @f() {\n^e:\n" ++
    String.join ((List.range n).map fun i => s!"  %c{i}: i32 = const {i} @0\n") ++
    "  ret @0\n}\n" ++ locsText

/-- An error's line, column and reason. -/
def errorShown (e : ParseError) : Nat × Nat × String := (e.pos.line, e.pos.col, e.reason)

/-- How the core dialect's parser rejects a text, or `none`. -/
def parseError (text : String) : Option (Nat × Nat × String) :=
  match Fir.parse (d := CoreDialect) text with
  | .ok _ => none
  | .error e => some (errorShown e)

/-- How `readText` rejects a text, or `none`. -/
def readTextError (text : String) : Option (Nat × Nat × String) :=
  match FirRef.readText text with
  | .ok _ => none
  | .error e => some (errorShown e)

/-- How the spec's lexer and reader reject a text, or `none`. -/
def specReadError (text : String) : Option (Nat × Nat × String) :=
  match Text.lex text >>= Text.readModule with
  | .ok _ => none
  | .error e => some (errorShown e)

/-- How the spec's lexer rejects a text, or `none`. -/
def lexError (text : String) : Option (Nat × Nat × String) :=
  match Text.lex text with
  | .ok _ => none
  | .error e => some (errorShown e)

/-! # Deep and long texts -/

#guard parseError (deepRegionsText 100000) = some (200003, 5, "value %x is not defined in @f")
#guard parseError (deepItemsText 100000) = some (2, 1, "a func's body holds blocks, not items")
#guard parseError (deepAttrText 100000) = some (3, 3,
  "op ret does not decode: the dialect has no op with this name and these attributes, " ++
    "operand types and result types")
#guard parseError (flatOpsText 100000) = none

-- The reader reads the deep items whole; the decoder is what rejects them.
#guard readTextError (deepItemsText 100000) = none

/-! # Errors -/

/-- A reader error at the start of a text, and a lexer error at its end. -/
def lateLexError : String := "}\n" ++ flatOpsText 1000 ++ "\x07"

#guard (lexError lateLexError).isSome
#guard parseError lateLexError = lexError lateLexError
#guard readTextError lateLexError = lexError lateLexError

/-- Texts that the readers reject, at their start, in the middle and at
their end, and texts that the lexer rejects. -/
def badTexts : List String :=
  ["", "}", "func", "func @f( {", "func @f() {\n^e:\n  ret @0\n", deepRegionsText 3 ++ "}",
    "func @f() {\n^e:\n  %a: i32 = const 1\n}\n" ++ locsText, deepAttrText 3 ++ "locs", "\"abc",
    "@99999999999", "func @f() -> i32 {\n^e:\n  ret 1 @0\n}\n" ++ locsText ++ "x", "- 1"]

#guard badTexts.all fun t => readTextError t = specReadError t
#guard [deepRegionsText 3, deepItemsText 3, deepAttrText 3, flatOpsText 3].all fun t =>
  readTextError t = specReadError t && (readTextError t).isNone

/--
info: 'FirRef.readModule_eq_readModule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FirRef.readModule_eq_readModule

/--
info: 'FirRef.readText_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FirRef.readText_eq

end FirTest
