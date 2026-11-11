import Fir
import FirRef.Utf8

/-!
Tests of the lexer and the readers that `fir-ref` runs: `FirRef.parse`
reads a text with `FirRef.readText`, which lexes over the text's positions
and reads with loops that take no stack per level of nesting. This module
imports `FirRef.Utf8`, as `fir-ref` does, so `Fir.parse` below runs as
`FirRef.parse`.

The spec's readers take stack per level of nesting. Here, in the
elaborator, they overflow the stack on attributes or items nested 800,000
levels deep and on regions nested 400,000 deep, and the build fails. The
first checks read deeper texts, one for each loop of the readers:
attributes, functions and modules nested 1,000,000 levels deep, through
`Fir.parse`, with the decoder's verdict on each, and regions nested 600,000
deep, with `readText` alone. The modules also need the decoder's loop,
which takes no stack per level of nested modules. They pass only because the readers that `fir-ref` runs
take no stack per level; through `Fir.parse`, they also need
`parse_eq_parse`.

A lexer error at the end of a text is reported before a reader error at
its start, as the spec reports it: `readText` runs the readers first, then
looks for a lexer error when they fail. On small texts, `readText` gives
what the spec's lexer and `Text.readModule` give, errors included; here
`Text.readModule` runs as `FirRef.readModule`, the same readers on a list
of tokens. The last checks pin the axioms of the theorems to Lean's
standard ones.
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

/-- `n` modules, each in the body of the one before, then an item of a
kind that no dialect registers. -/
def deepModulesText (n : Nat) : String :=
  String.join (List.replicate n "module @a() {\n") ++ String.join (List.replicate n "}\n") ++
    "bad @b() {\n}\n" ++ locsText

/-- An op whose attribute is applied `n` levels deep. -/
def deepAttrText (n : Nat) : String :=
  "func @f() {\n^e:\n  ret " ++ String.join (List.replicate n "h(") ++ "x" ++
    String.join (List.replicate n ")") ++ " @0\n}\n" ++ locsText

/-- An item of a dialect's kind whose attribute is applied `n` levels deep.
Every reader decodes it, whatever its dialect, and keeps the attribute. -/
def deepItemAttrText (n : Nat) : String :=
  "toy.cell @c() " ++ String.join (List.replicate n "h(") ++ "x" ++
    String.join (List.replicate n ")") ++ " {\n}\n" ++ locsText

/-- What the core dialect's check reports on a text, as `fir-ref validate`
runs it, or `none` when the text does not parse. -/
def checkMessages (text : String) : Option (List String) :=
  match Fir.parse (d := CoreDialect) text with
  | .ok m => some ((m.problems ++ m.setProblems).map (·.message))
  | .error _ => none

/-- Whether the core dialect's printer gives a text back. -/
def printsBack (text : String) : Bool :=
  match Fir.parse (d := CoreDialect) text with
  | .ok m => m.print == text
  | .error _ => false

/-- A block of `n` constants. -/
def flatOpsText (n : Nat) : String :=
  "func @f() {\n^e:\n" ++
    String.join ((List.range n).map fun i => s!"  %c{i}: i32 = const {i} @0\n") ++
    "  ret @0\n}\n" ++ locsText

/-- A function whose blocks branch: an op with an operand, then successors
with and without arguments. -/
def branchText (succ : String) : String :=
  "func @f(%c: i1) {\n^e:\n  cond_br %c, ^a(%c), " ++ succ ++ " @0\n^a(%x: i1):\n" ++
    "  br ^b @0\n^b:\n  ret @0\n}\n" ++ locsText

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

/-! # Deep texts -/

-- `attrLoop`: the readers read the attribute whole, and the decoder rejects the op.
#guard parseError (deepAttrText 1000000) = some (3, 3,
  "op ret does not decode: the dialect has no op with this name and these attributes, " ++
    "operand types and result types")
-- `itemsLoop`: the readers read the items whole, and the decoder rejects the first.
#guard parseError (deepItemsText 1000000) = some (2, 1, "a func's body holds blocks, not items")
-- `itemsLoop` and `decodeLoop`: the readers read the modules whole, and the
-- decoder decodes them whole before it rejects the item after them.
#guard parseError (deepModulesText 1000000) = some (2000001, 1,
  "unknown item kind bad: the kinds are func, module and the words of dialects")
-- `attrLoop`, `decodeLoop`, `writableLoop`, `dialectsLoop` and `printAttrs`: the
-- readers read the item's attribute whole, the decoder keeps it, the check
-- walks it with no stack per level, and the printer writes it back.
#guard checkMessages (deepItemAttrText 1000000) = some [
  "no dialect registers the kind of item \"toy.cell\"",
  "the item writes a word of the dialect toy, which the module's dialect set does not name"]
#guard printsBack (deepItemAttrText 1000000)
-- `blocksLoop`: the readers read the regions whole.
#guard readTextError (deepRegionsText 600000) = none

/-! # Errors -/

/-- A reader error at the start of a text, and a lexer error at its end. -/
def lateLexError : String := "}\n" ++ flatOpsText 1000 ++ "\x07"

#guard (lexError lateLexError).isSome
#guard parseError lateLexError = lexError lateLexError
#guard readTextError lateLexError = lexError lateLexError

/-- A text that the readers read up to a lexer error at its end, in a
comment: they stop there, and the lexer's error is reported. -/
def endLexError : String := flatOpsText 1000 ++ "// a\x07\n"

#guard (lexError endLexError).isSome
#guard parseError endLexError = lexError endLexError
#guard readTextError endLexError = lexError endLexError

/-- Texts that the readers reject, at their start, in the middle and at
their end, some after a comment with characters of several bytes, in an
op's successors, and texts that the lexer rejects. -/
def badTexts : List String :=
  ["", "}", "func", "func @f( {", "func @f() {\n^e:\n  ret @0\n", deepRegionsText 3 ++ "}",
    "func @f() {\n^e:\n  %a: i32 = const 1\n}\n" ++ locsText, deepAttrText 3 ++ "locs", "\"abc",
    "@99999999999", "func @f() -> i32 {\n^e:\n  ret 1 @0\n}\n" ++ locsText ++ "x", "- 1",
    "// a\x07b\n" ++ locsText, "func @f() {\n// é" ++ String.singleton (Char.ofNat 0x1F600) ++ "x",
    "func @f() {\n// é\n}", branchText "%c", branchText "^b(", branchText "^b(%c,"]

#guard badTexts.all fun t => readTextError t = specReadError t && (readTextError t).isSome
#guard [deepRegionsText 3, deepItemsText 3, deepModulesText 3, deepAttrText 3, flatOpsText 3,
    branchText "^b"].all fun t =>
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
