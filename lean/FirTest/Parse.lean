import Fir
import FirRef.Utf8

/-!
Tests of the parser (`Fir.parse`). Each case of the grammar section's list
of texts that do not decode, and each lexical and grammar error, is checked
with the position of its error. The texts and positions are those of
`crates/funk-ir/tests/parse_errors.rs`, so the two parsers reject each one
at the same place. Characters that the repository's hooks keep out of files
are written as Lean escapes.
-/

namespace FirTest

open Fir

/-- Parses with the core dialect. -/
def parseCore (t : String) : Except ParseError (Module CoreDialect) := parse t

/-- The text parses. -/
def accepts (t : String) : Bool := (parseCore t).toBool

/-- The text parses and prints as itself. -/
def roundTrips (t : String) : Bool :=
  match parseCore t with
  | .ok m => m.print == t
  | .error _ => false

/-- The text parses and prints as `canonical`. -/
def printsAs (t canonical : String) : Bool :=
  match parseCore t with
  | .ok m => m.print == canonical
  | .error _ => false

/-- The text is rejected at `line:col`, for a reason that holds `needle`. -/
def rejectedAt (t : String) (line col : Nat) (needle : String) : Bool :=
  match parseCore t with
  | .error e => e.pos == ⟨line, col⟩ && (e.reason.splitOn needle).length > 1
  | .ok _ => false

/-- One function, followed by a location table with `@0`. -/
def oneFunc (f : String) : String := f ++ "\nlocs {\n  @0 = unknown\n}\n"

/-- `@f(%a: i32) -> i32` whose entry block holds `ops`, one per line from
line 3. -/
def func (ops : List String) : String :=
  oneFunc ("func @f(%a: i32) -> i32 {\n^entry:\n" ++ String.join (ops.map ("  " ++ · ++ "\n")) ++ "}\n")

/-- A function whose symbol is `s`, written between quotes. -/
def quoted (s : String) : String := oneFunc ("func @\"" ++ s ++ "\"() {\n^e:\n  ret @0\n}\n")

/-- A canonical text. -/
def seven : String :=
  "func @seven() -> i32 {\n^entry:\n  %c: i32 = const 7 @0\n  ret %c @0\n}\n\nlocs {\n  @0 = unknown\n}\n"

/-! # Texts that parse -/

#guard roundTrips seven && roundTrips "locs {\n}\n" && roundTrips Example.sumModule.print
-- No final line feed.
#guard printsAs (String.ofList seven.toList.dropLast) seven && printsAs "locs {\n}" "locs {\n}\n"
#guard printsAs (seven ++ "// a comment at the end") seven
#guard printsAs (seven.replace "^entry:" "^entry: // \"quotes\", \\ and é\t") seven
#guard printsAs (seven.replace "@0\n  ret" "@0\n\tret") seven
#guard printsAs (func ["%c: i32 = const-1 @0", "ret %c @0"])
  (func ["%c: i32 = const -1 @0", "ret %c @0"])
#guard accepts (oneFunc "func @f(%a: i0, %p: ptr) {\n^e:\n  ret @0\n}\n")
#guard accepts (oneFunc "func @f(%a: i16777215) {\n^e:\n  ret @0\n}\n")
#guard accepts (func ["%c: i16777215 = const 99999999999999999999999999999999999999999 @0",
  "ret %a @0"])
#guard accepts "func @f() {\n^e:\n  ret @4294967295\n}\n\nlocs {\n  @4294967295 = unknown\n}\n"
#guard accepts (quoted "\\u{0}\\u{7f}\\u{2028}\\u{e007f}\\\\\\\"")
-- Every op of the core dialect, and ops of no dialect's choosing in the
-- grammar: regions, successors and applied attributes all parse.
#guard roundTrips (oneFunc ("func @g(%a: i8, %c: i1) -> i8 {\n^entry:\n" ++
  "  %s: i8 = sub nuw nsw %a, %a @0\n  %f: i8 = freeze %s @0\n" ++
  "  cond_br %c, ^x(%f), ^y @0\n^x(%v: i8):\n  ret %v @0\n^y:\n  ret %a @0\n}\n"))
#guard roundTrips (oneFunc "func @g() {\n^entry:\n  br {\n    ^inner:\n      ret @0\n  } @0\n}\n")

/-! # A number out of its range, at the number -/

#guard rejectedAt (func ["ret %a @4294967296"]) 3 11 "out of range"
#guard rejectedAt "locs {\n  @4294967296 = unknown\n}\n" 2 4 "out of range"
#guard rejectedAt "locs {\n  @0 = \"f\":4294967296:1 to 1:1\n}\n" 2 12 "line 4294967296 is out of range"
#guard rejectedAt "locs {\n  @0 = \"f\":1:1 to 1:99999999999999999999\n}\n" 2 21 "column"
#guard rejectedAt (oneFunc "func @f(%a: i16777216) {\n^e:\n  ret @0\n}\n") 1 13 "does not decode"

/-! # A string or symbol not in its one spelling -/

#guard rejectedAt (oneFunc "func @\"sum\"() {\n^e:\n  ret @0\n}\n") 1 6 "is written @sum"
#guard [("\\u{41}", "written as itself"), ("\\u{9}", "is written \\t"),
    ("\\u{a}", "is written \\n"), ("\\u{001}", "leading zero"),
    ("\\u{1F}", "lowercase hexadecimal"), ("\\u{}", "lowercase hexadecimal"),
    ("\\u{d800}", "not a Unicode scalar value"), ("\\u{110000}", "not a Unicode scalar value"),
    ("\\x41", "a string escape is"), ("\\r", "a string escape is")].all
  fun (s, needle) => rejectedAt (quoted s) 1 8 needle
#guard rejectedAt (quoted "a\tb") 1 9 "U+0009 must be escaped"
#guard rejectedAt (quoted "\u202e") 1 8 "U+202E must be escaped"
#guard rejectedAt (quoted "\u0085") 1 8 "U+0085 must be escaped"
#guard rejectedAt "locs {\n  @0 = name(\"open\n" 2 18 "must be escaped"
#guard rejectedAt "locs {\n  @0 = name(\"open" 2 13 "not closed"

/-! # An item of a kind the parser does not know -/

#guard rejectedAt (oneFunc "global @g() {\n}\n") 1 1 "unknown item kind global"
#guard rejectedAt (oneFunc "func @f() inline {\n^e:\n  ret @0\n}\n") 1 11 "no attributes"
#guard rejectedAt (oneFunc "func @f() {\n  func @g() {\n  }\n}\n") 2 3 "blocks, not items"
#guard rejectedAt (oneFunc "module @m() {\n  func @g() {\n  }\n}\n") 1 1 "unknown item kind module"

/-! # A type that does not decode -/

#guard ["i032", "i00", "u8", "index", "i32(1)", "i"].all fun ty =>
  rejectedAt (oneFunc ("func @f(%a: " ++ ty ++ ") {\n^e:\n  ret @0\n}\n")) 1 13 "does not decode"
#guard rejectedAt (oneFunc "func @f() -> f32 {\n^e:\n  ret @0\n}\n") 1 14 "does not decode"
#guard rejectedAt (func ["%c: i8x = const 1 @0", "ret %a @0"]) 3 7 "does not decode"

/-! # A value defined twice, at its second definition -/

#guard rejectedAt (func ["%a: i32 = const 1 @0", "ret %a @0"]) 3 3 "%a is defined twice"
#guard rejectedAt (func ["%b: i32 = const 1 @0", "%b: i32 = const 2 @0", "ret %b @0"]) 4 3 "%b"
#guard rejectedAt (oneFunc "func @f(%a: i8, %a: i8) {\n^e:\n  ret @0\n}\n") 1 17 "%a is defined twice"
#guard rejectedAt (oneFunc "func @f(%a: i8) {\n^e:\n  ret @0\n^b(%a: i8):\n  ret @0\n}\n") 4 4
  "%a is defined twice"

/-! # An operand that the function does not define -/

#guard rejectedAt (func ["%c: i32 = add %a, %nope @0", "ret %c @0"]) 3 21 "%nope is not defined in @f"
#guard rejectedAt (oneFunc
  "func @g(%x: i32) {\n^e:\n  ret @0\n}\n\nfunc @h() -> i32 {\n^e:\n  ret %x @0\n}\n") 8 7
  "%x is not defined in @h"
#guard rejectedAt (oneFunc "func @\"1\"() {\n^e:\n  ret %x @0\n}\n") 3 7 "%x is not defined in @\"1\""
-- A symbol in a reason is spelled canonically, so the reason holds no
-- character that a string escapes.
#guard match parseCore (oneFunc "func @\"a\\nb\\u{1b}[31m\\u{202e}x\"() {\n^e:\n  ret %x @0\n}\n") with
  | .error e => e.reason.endsWith "is not defined in @\"a\\nb\\u{1b}[31m\\u{202e}x\"" &&
      !e.reason.any Text.isEscaped
  | .ok _ => false

/-! # An op that does not decode, at its name -/

#guard [("%c: i32 = add %a, %b @0", true), ("%c: i32 = add %a @0", false),
    ("%c: i32 = add %a, %a, %a @0", false), ("%c: i64 = add %a, %a @0", false),
    ("%c: i32 = add nsw nuw %a, %a @0", false), ("%c: i32 = add exact %a, %a @0", false),
    ("%c: i1 = const 1 @0", false), ("%c: i1 = const -1 @0", false),
    ("%c: i8 = const 128 @0", false), ("%c: i8 = const -129 @0", false),
    ("%c: i8 = const true @0", false), ("%c: i8 = const @0", false),
    ("%c: i8 = const 1 2 @0", false), ("%c: i8 = const \"1\" @0", false),
    ("%c: i8 = const 1 %a @0", false), ("%c: ptr = const 1 @0", false),
    ("%c: i8, %d: i8 = const 1 @0", false), ("%c: i8 = ret @0", false),
    ("ret nsw %a @0", false), ("%c: i8 = toy.mix %a @0", false)].all fun (op, b64) =>
  let first := if b64 then "%b: i64 = const 0 @0" else "%z: i1 = const true @0"
  let col := match op.splitOn "=" with
    | before :: _ :: _ => before.length + 5
    | _ => 3
  rejectedAt (func [first, op, "ret %a @0"]) 4 col "does not decode"
#guard rejectedAt (func ["%c: i8 = const 99999999999999999999999999999999999999999 @0"]) 3 12
  "does not decode"

/-! # Characters not allowed outside strings, even in comments -/

#guard rejectedAt (seven.replace "\n" "\r\n") 1 23 "U+000D is not allowed outside strings"
#guard rejectedAt ("\ufeff" ++ seven) 1 1 "U+FEFF"
#guard rejectedAt ("// \u202e reversed\n" ++ seven) 1 4 "U+202E"
#guard rejectedAt ("// \u2066\n" ++ seven) 1 4 "U+2066"
#guard rejectedAt (seven.replace "@0\n  ret" "@0 // \u200e\n  ret") 3 27 "U+200E"
#guard rejectedAt (seven.replace "^entry:" "^entry:\u2028") 2 8 "U+2028"
#guard rejectedAt (seven.replace "^entry:" "^entry:\u0085") 2 8 "U+0085"
#guard rejectedAt (seven.replace "^entry:" "^entry:\u000b") 2 8 "U+000B"

/-! # Tokens that run into name characters -/

#guard rejectedAt (func ["ret %a @1x"]) 3 11 "must not run into"
#guard rejectedAt (func ["%c: i32 = const 1.5 @0", "ret %c @0"]) 3 19 "float"
#guard rejectedAt (func ["%c: i32 = const 1abc @0", "ret %c @0"]) 3 19 "must not run into"
#guard rejectedAt (func ["%c: i32 = const 007 @0", "ret %c @0"]) 3 19 "leading zeros"
#guard rejectedAt (func ["ret %a @01"]) 3 11 "must not run into"
#guard rejectedAt (func ["%c: i32 = const -0 @0", "ret %c @0"]) 3 19 "-0 is not an integer"
#guard rejectedAt (func ["%c: i32 = const - 1 @0", "ret %c @0"]) 3 19 "negative integer"
#guard rejectedAt (func ["% c: i32 = const 1 @0"]) 3 3 "% must be followed by a value name"
#guard rejectedAt (func ["ret %a @ 0"]) 3 10 "@ must be followed"
#guard rejectedAt (func ["ret %a @0 #"]) 3 13 "unexpected character U+0023"
#guard rejectedAt (func ["ret %a @0 /"]) 3 13 "unexpected character U+002F"

/-! # Texts that break the grammar -/

#guard rejectedAt "" 1 1 "the location table"
#guard rejectedAt "locs {\n}\nfunc" 3 1 "the end of the text"
#guard rejectedAt (func ["ret %a"]) 4 1 "location reference"
#guard rejectedAt (oneFunc "func @f() {\n^e():\n  ret @0\n}\n") 2 4 "value definition"
#guard rejectedAt (oneFunc "func @f() {\n^e:\n  ret ^x() @0\n}\n") 3 10 "a value passed to the successor"
#guard rejectedAt (oneFunc "func @f() {\n^e:\n  ret ^x, %a @0\n}\n") 3 11 "a successor"
#guard rejectedAt (oneFunc "func f() {\n}\n") 1 6 "symbol"
#guard rejectedAt (oneFunc "func @f() {\n^e:\n  %x = const 1 @0\n}\n") 3 6 ": and the value's type"
#guard rejectedAt "locs {\n  @0 = somewhere\n}\n" 2 8 "not a kind of location"
#guard rejectedAt "locs {\n  @0 = \"f\":-1:1 to 1:1\n}\n" 2 12 "a line"
#guard rejectedAt "locs {\n  @0 = name(x)\n}\n" 2 13 "the name, as a string"
#guard rejectedAt "locs {\n  @0 = fused(@1 @2)\n}\n" 2 17 ")"

/-! # Bytes that are not UTF-8, where they start -/

#guard match FirRef.parseBytes (d := CoreDialect)
    ("locs {\n  @0 = name(\"a".toUTF8 ++ ⟨#[0xff]⟩ ++ "b\")\n}\n".toUTF8) with
  | .error e => e.pos == ⟨2, 15⟩
  | .ok _ => false
#guard match FirRef.parseBytes (d := CoreDialect) ("// é\n".toUTF8 ++ ⟨#[0xc3]⟩) with
  | .error e => e.pos == ⟨2, 1⟩
  | .ok _ => false
#guard (FirRef.parseBytes (d := CoreDialect) seven.toUTF8).toBool

end FirTest
