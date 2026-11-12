import Fir.Text.RoundTrip

/-!
The parser reads a text into a module of any dialect, in three steps. It
reads the characters into tokens, below. It then reads the tokens by the
grammar of a module, which is the same for every dialect, into a syntax
tree that leaves types, attributes and ops generic. Last, it decodes that
tree through the dialect: each type with the dialect's reader of types, and
each op with its reader of ops, from its name, its attributes and the types
of its operands and results. Each step stops at its first error, and the
steps run in the order of `funk`'s
(`docs/decisions/rust-ir-and-tools-funk.md#report-format`), so the two
parsers reject a text with one error at the same position. A text with
several errors is rejected at the first error of the earliest step; the two
parsers may then report different errors, which that page allows.

Each step is a total function: it never loops and never fails for want of
fuel, and the proof that parsing a printed module gives the module back
unfolds it case by case. The parser has no code for any particular op, type
or dialect, so it reads every op of every dialect; the core dialect is one
instance of a dialect's text.

# Reading tokens

The lexer reads the characters of a text from first to last, and gives each
token the position where it starts: its line from 1, and its column in UTF-8
bytes from 1, as a location counts them. Whitespace and comments are
dropped. Every character outside strings, in comments too, must be one that
a text may hold outside strings. The list of tokens always ends with the end
token, at the position where the text ends, so that an error found there has
a position too.

This part gives the tokens and their positions, then reads strings, then
numbers, names and symbols, and last the tokens of a whole text.
-/

namespace Fir.Text

/-- A token. Numbers are read whole: a location reference below `2^32`,
and an integer of any size. A float literal is kept as it is written. -/
inductive Tok where
  | value (name : Name)
  | label (name : Name)
  | sym (name : String)
  | locRef (r : Nat)
  | word (w : String)
  | int (i : Int)
  | str (s : String)
  | lparen | rparen | lbrace | rbrace | comma | colon | eq | arrow
  | eof
  | float (l : FloatLit)
  deriving Repr, DecidableEq, Inhabited

/-- How an error message names a token. Strings and symbols are spelled
canonically, so a message never holds a character that a string escapes. -/
def Tok.describe : Tok → String
  | .value n => "value %" ++ n
  | .label n => "label ^" ++ n
  | .sym s => "symbol " ++ printSymbol s
  | .locRef r => s!"location reference @{r}"
  | .word w => "word " ++ w
  | .int i => s!"integer {i}"
  | .str s => "string " ++ quote s
  | .lparen => "(" | .rparen => ")" | .lbrace => "{" | .rbrace => "}"
  | .comma => "," | .colon => ":" | .eq => "=" | .arrow => "->"
  | .eof => "the end of the text"
  | .float l => "float literal " ++ l.print

/-- A token and the position where it starts. -/
structure Token where
  tok : Tok
  pos : TextPos
  deriving Repr, DecidableEq

/-- The position `n` bytes further along the same line. -/
def _root_.Fir.TextPos.advance (p : TextPos) (n : Nat) : TextPos := { p with col := p.col + n }

/-- The size of some characters in UTF-8, in bytes. -/
def utf8Len (cs : List Char) : Nat := (cs.map Char.utf8Size).sum

/-- How a message names a character: `U+000D`. -/
def codePoint (c : Char) : String :=
  let digits := (hex c.toNat).toUpper
  "U+" ++ "".pushn '0' (4 - digits.length) ++ digits

/-- An error at a position. -/
def errorAt (p : TextPos) (reason : String) : Except ParseError α := .error ⟨p, reason⟩

/-- The characters after the leading ones that satisfy `f`: a suffix, so
never more. -/
theorem length_dropWhile_le (f : Char → Bool) (cs : List Char) :
    (cs.dropWhile f).length ≤ cs.length :=
  (List.dropWhile_suffix f).length_le

/-- The characters after a token: never more than were given. -/
abbrev Left (cs : List Char) := { r : List Char // r.length ≤ cs.length }

/-- The value of some hexadecimal digits. -/
def hexValue (ds : List Char) : Nat :=
  ds.foldl (fun n c => 16 * n + if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10) 0

/-!
# Strings

A string holds any character but `"`, `\` and the characters that it
escapes. Each escape has one spelling, the one that the printer writes. A
string that is not in its one spelling is an error at the start of the
escape, or at the character that should have been escaped.
-/

/-- The character that `\u{h}` stands for, with `h` the given digits, if
the escape is in its one spelling. `p` is the position of its backslash. -/
def unicodeEscape (digits : List Char) (p : TextPos) : Except ParseError Char :=
  let n := hexValue digits
  let shown := "\\u{" ++ String.ofList digits ++ "}"
  if digits.isEmpty then errorAt p "\\u{ must be followed by lowercase hexadecimal digits and }"
  else if h : ¬ n.isValidChar then errorAt p (shown ++ " is not a Unicode scalar value")
  else
    let c := Char.ofNatAux n (Classical.not_not.mp h)
    if digits.length > 1 && digits.head? = some '0' then
      errorAt p (shown ++ " has a leading zero: write \\u{" ++ hex n ++ "}")
    else if c = '\n' then errorAt p (codePoint c ++ " is written \\n in a string")
    else if c = '\t' then errorAt p (codePoint c ++ " is written \\t in a string")
    else if isEscaped c then .ok c
    else errorAt p (codePoint c ++ " is written as itself, not as an escape")

/-- Reads one escape after its backslash at `p`: the character it stands
for, its width after the backslash in bytes (an escape is ASCII), and the
characters after it. -/
def lexEscape (cs : List Char) (p : TextPos) :
    Except ParseError (Char × Nat × { r : List Char // r.length < cs.length }) :=
  match cs with
  | '\\' :: rest => .ok ('\\', 1, ⟨rest, by simp⟩)
  | '"' :: rest => .ok ('"', 1, ⟨rest, by simp⟩)
  | 'n' :: rest => .ok ('\n', 1, ⟨rest, by simp⟩)
  | 't' :: rest => .ok ('\t', 1, ⟨rest, by simp⟩)
  | 'u' :: '{' :: rest =>
    match h : rest.dropWhile isHexDigit with
    | '}' :: after =>
      have : after.length < ('u' :: '{' :: rest).length := by
        have h1 := length_dropWhile_le isHexDigit rest
        rw [h] at h1
        simp at h1 ⊢
        omega
      let digits := rest.takeWhile isHexDigit
      (unicodeEscape digits p).map (·, 3 + digits.length, ⟨after, this⟩)
    | _ => errorAt p "\\u{ must be followed by lowercase hexadecimal digits and }"
  | _ => errorAt p "a string escape is \\\\, \\\", \\n, \\t or \\u{h}"

/-- Reads the characters of a string from `cs` at `p`, for `lexString`.
`cs` is what is left of `cs₀`, the characters after the opening quote, so
what follows the closing quote is left of `cs₀` too. The result says so
directly, so the recursive call is the last step: a string of any length
takes no stack. `acc` holds the characters read so far, last first. -/
def lexStringFrom (cs₀ cs : List Char) (h : cs.length ≤ cs₀.length) (p start : TextPos)
    (acc : List Char) : Except ParseError (String × Left cs₀ × TextPos) :=
  match cs, h with
  | [], _ => errorAt start "the string is not closed"
  | '"' :: rest, h => .ok (String.ofList acc.reverse, ⟨rest, by simp at h; omega⟩, p.advance 1)
  | '\\' :: rest, h => do
    let (c, width, ⟨after, ha⟩) ← lexEscape rest p
    lexStringFrom cs₀ after (by simp at h; omega) (p.advance (1 + width)) start (c :: acc)
  | c :: rest, h =>
    if isEscaped c then errorAt p (codePoint c ++ " must be escaped in a string")
    else lexStringFrom cs₀ rest (by simp at h; omega) (p.advance c.utf8Size) start (c :: acc)
termination_by cs.length
decreasing_by all_goals (simp_wf <;> omega)

/-- Reads the rest of a string that opened at `start`, from position `p`:
the characters it holds, the characters after its closing quote, and the
position there. -/
def lexString (cs : List Char) (p start : TextPos) : Except ParseError (String × Left cs × TextPos) :=
  lexStringFrom cs cs (Nat.le_refl _) p start []

/-!
# Numbers, names and symbols

A number has no leading zeros, and no token that holds a name or a number
runs into a name character: maximal munch reads a name character after it as
part of it, so `@1x`, `007` and `1.5x` are errors at the number. A location
reference is below 2³² (ADR-2026-10-29-2007); an integer has no limit here, since the
dialect that reads it bounds it. A whole number followed by `.` and a
digit, or `0` followed by `x`, is the start of a float literal, read whole
as it is written; the core dialect bounds it (ADR-2026-11-11-1438).
-/

/-- Why a number may not end where it does: it runs into the name
character `c`. -/
def runsInto (c : Char) : String :=
  "a number must not run into the name character '" ++ c.toString ++ "': numbers have no leading zeros"

/-- Checks that a number ends before `cs`: `cs` is empty or starts with a
character that is no name character. -/
def lexEnd (cs : List Char) (p : TextPos) : Except ParseError Unit :=
  match cs with
  | c :: _ => if isNameChar c then errorAt p (runsInto c) else .ok ()
  | [] => .ok ()

/-- The digits of a number at `p` that starts with the digit `d`, followed
by `cs`, and the characters after them. -/
def lexDigits (d : Char) (cs : List Char) (p : TextPos) : Except ParseError (List Char × Left cs) :=
  let ds := if d = '0' then ['0'] else d :: cs.takeWhile Char.isDigit
  let rest : Left cs :=
    if d = '0' then ⟨cs, by simp⟩ else ⟨cs.dropWhile Char.isDigit, length_dropWhile_le _ _⟩
  match rest.1 with
  | c :: _ => if isNameChar c then errorAt p (runsInto c) else .ok (ds, rest)
  | [] => .ok (ds, rest)

/-- The value of some decimal digits. A long number is read in two halves,
joined by one product, so that a constant of millions of digits, as wide
types allow, is read in about the time of a few products, not in time
quadratic in its length. -/
def digitsValue (ds : List Char) : Nat :=
  if ds.length ≤ 64 then ds.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0
  else
    let k := ds.length / 2
    digitsValue (ds.take (ds.length - k)) * 10 ^ k + digitsValue (ds.drop (ds.length - k))
termination_by ds.length
decreasing_by all_goals (simp_wf; omega)

/-- Reads what follows `@` at `p`: a location reference, or a symbol written
as a word or quoted. A quoted name that is a word is an error: it is written
bare. -/
def lexAt (cs : List Char) (p : TextPos) : Except ParseError (Tok × Left cs × TextPos) :=
  match cs with
  | c :: rest =>
    if c.isDigit then do
      let q := p.advance 1
      let (ds, ⟨r, hr⟩) ← lexDigits c rest q
      let n := digitsValue ds
      if n < Location.limit then pure (.locRef n, ⟨r, by simp; omega⟩, q.advance ds.length)
      else errorAt q s!"location reference @{n} is out of range: it must be below 2^32"
    else if isWordStart c then
      let w := rest.takeWhile isNameChar
      .ok (.sym (String.ofList (c :: w)), ⟨rest.dropWhile isNameChar,
        by have := length_dropWhile_le isNameChar rest; simp; omega⟩, p.advance (2 + w.length))
    else if c = '"' then do
      let (s, ⟨r, hr⟩, q) ← lexString rest (p.advance 2) (p.advance 1)
      if isWord s then errorAt p ("the symbol @\"" ++ s ++ "\" is written @" ++ s)
      else pure (.sym s, ⟨r, by simp; omega⟩, q)
    else errorAt p "@ must be followed by a symbol or a location reference"
  | [] => errorAt p "@ must be followed by a symbol or a location reference"

/-- Reads an integer at `p` whose first digit `d` is followed by `cs`; `neg`
says whether a `-` came before `d`. -/
def lexInt (neg : Bool) (d : Char) (cs : List Char) (p : TextPos) :
    Except ParseError (Tok × Left cs × TextPos) := do
  let (ds, rest) ← lexDigits d cs p
  let n : Int := digitsValue ds
  pure (.int (if neg then -n else n), rest, p.advance ((if neg then 1 else 0) + ds.length))

/-- Reads what may follow the fraction of a decimal float literal at `p`:
`e` and its exponent, an integer with no leading zeros that is not `-0`, or
nothing; then the literal must end. -/
def lexExponent (cs : List Char) (p : TextPos) : Except ParseError (Option Int × Left cs) :=
  match cs with
  | 'e' :: '-' :: x :: r =>
    if x = '0' then errorAt p "-0 is not an exponent"
    else if x.isDigit then do
      let (ds, ⟨r', h⟩) ← lexDigits x r p
      pure (some (-(digitsValue ds : Int)), ⟨r', by simp; omega⟩)
    else errorAt p (runsInto 'e')
  | 'e' :: x :: r =>
    if x.isDigit then do
      let (ds, ⟨r', h⟩) ← lexDigits x r p
      pure (some (digitsValue ds), ⟨r', by simp; omega⟩)
    else errorAt p (runsInto 'e')
  | cs => (lexEnd cs p).map fun _ => (none, ⟨cs, Nat.le_refl _⟩)

/-- Reads the hexadecimal digits of a float literal after its `0x`, from
`cs` at `p`, where the literal starts. -/
def lexHex (cs : List Char) (p : TextPos) : Except ParseError (Tok × Left cs × TextPos) :=
  let ds := cs.takeWhile isHexDigit
  if ds.isEmpty then errorAt p "0x must be followed by lowercase hexadecimal digits"
  else
    (lexEnd (cs.dropWhile isHexDigit) p).map fun _ =>
      (.float (.hex ds), ⟨cs.dropWhile isHexDigit, length_dropWhile_le _ _⟩, p.advance (2 + ds.length))

/-- Reads the fraction of a decimal float literal from `c :: cs`, after
its `.`, and what follows it. The literal starts at `p`, with `-` when
`neg`, and its whole part is `whole`. -/
def lexFraction (neg : Bool) (whole : Nat) (c : Char) (cs : List Char) (p : TextPos) :
    Except ParseError (Tok × Left cs × TextPos) := do
  let (exp, ⟨r, h⟩) ← lexExponent (cs.dropWhile Char.isDigit) p
  let l := FloatLit.dec neg whole (c :: cs.takeWhile Char.isDigit) exp
  pure (.float l, ⟨r, Nat.le_trans h (length_dropWhile_le _ _)⟩, p.advance l.print.length)

/-- What follows the whole part of a number whose first digit `d` is
followed by `cs`: the whole part is `0`, or `d` and the digits after it. -/
def afterWhole (d : Char) (cs : List Char) : List Char :=
  if d = '0' then cs else cs.dropWhile Char.isDigit

/-- The value of the whole part of a number whose first digit `d` is
followed by `cs`. -/
def wholeValue (d : Char) (cs : List Char) : Nat :=
  if d = '0' then 0 else digitsValue (d :: cs.takeWhile Char.isDigit)

theorem length_afterWhole (d : Char) (cs : List Char) : (afterWhole d cs).length ≤ cs.length := by
  unfold afterWhole
  split
  · exact Nat.le_refl _
  · exact length_dropWhile_le _ _

/-- Reads a float literal at `p` whose whole part starts with the digit
`d`, followed by `cs`, with `-` before `d` when `neg`; or `none` when what
follows the whole part does not start a float literal. -/
def lexFloat (neg : Bool) (d : Char) (cs : List Char) (p : TextPos) :
    Option (Except ParseError (Tok × Left cs × TextPos)) :=
  match h : afterWhole d cs with
  | '.' :: c :: r =>
    if c.isDigit then
      some ((lexFraction neg (wholeValue d cs) c r p).map fun (t, ⟨r', h'⟩, q) =>
        (t, ⟨r', by have := length_afterWhole d cs; rw [h] at this; simp at this; omega⟩, q))
    else none
  | 'x' :: r =>
    if d = '0' ∧ neg = false then
      some ((lexHex r p).map fun (t, ⟨r', h'⟩, q) =>
        (t, ⟨r', by have := length_afterWhole d cs; rw [h] at this; simp at this; omega⟩, q))
    else none
  | _ => none

/-- Reads a number at `p` whose first digit `d` is followed by `cs`, with
`-` before `d` when `neg`: a float literal, or else an integer. -/
def lexNumber (neg : Bool) (d : Char) (cs : List Char) (p : TextPos) :
    Except ParseError (Tok × Left cs × TextPos) :=
  match lexFloat neg d cs p with
  | some r => r
  | none => lexInt neg d cs p

/-!
# The tokens of a text
-/

/-- Reads the token that starts with `c` at `p`, followed by `cs`: the token,
the characters after it, and the position there. `c` is not whitespace and
does not start a comment. -/
def lexToken (c : Char) (cs : List Char) (p : TextPos) : Except ParseError (Tok × Left cs × TextPos) :=
  let punct : Option Tok := match c with
    | '(' => some .lparen | ')' => some .rparen | '{' => some .lbrace | '}' => some .rbrace
    | ',' => some .comma | ':' => some .colon | '=' => some .eq | _ => none
  if !allowedOutsideStrings c then errorAt p (codePoint c ++ " is not allowed outside strings")
  else if let some t := punct then .ok (t, ⟨cs, by simp⟩, p.advance 1)
  else if c = '%' ∨ c = '^' then
    let n := cs.takeWhile isNameChar
    let rest : Left cs := ⟨cs.dropWhile isNameChar, length_dropWhile_le _ _⟩
    if n.isEmpty then
      errorAt p (if c = '%' then "% must be followed by a value name" else "^ must be followed by a label")
    else
      let name := String.ofList n
      .ok (if c = '%' then .value name else .label name, rest, p.advance (1 + n.length))
  else if c = '@' then lexAt cs p
  else if c = '"' then do
    let (s, rest, q) ← lexString cs (p.advance 1) p
    pure (.str s, rest, q)
  else if c = '-' then
    match cs with
    | '>' :: rest => .ok (.arrow, ⟨rest, by simp⟩, p.advance 2)
    | '0' :: rest =>
      match lexFloat true '0' rest p with
      | some r => do
        let (t, ⟨r, hr⟩, q) ← r
        pure (t, ⟨r, by simp; omega⟩, q)
      | none => errorAt p "-0 is not an integer"
    | d :: rest =>
      if d.isDigit then do
        let (t, ⟨r, hr⟩, q) ← lexNumber true d rest p
        pure (t, ⟨r, by simp; omega⟩, q)
      else errorAt p "- must start a negative number or ->"
    | [] => errorAt p "- must start a negative number or ->"
  else if c.isDigit then lexNumber false c cs p
  else if isWordStart c then
    let w := cs.takeWhile isNameChar
    .ok (.word (String.ofList (c :: w)), ⟨cs.dropWhile isNameChar, length_dropWhile_le _ _⟩,
      p.advance (1 + w.length))
  else errorAt p ("unexpected character " ++ codePoint c)

/-- A character other than the line feed, which ends a comment. -/
def notLineFeed (c : Char) : Bool := c != '\n'

/-- The first character in `cs` that is not allowed outside strings, with
its offset in bytes. -/
def firstDisallowed : List Char → Nat → Option (Char × Nat)
  | [], _ => none
  | c :: cs, n => if allowedOutsideStrings c then firstDisallowed cs (n + c.utf8Size) else some (c, n)

/-- Reads the tokens of `cs`, which starts at `p`. `acc` holds the tokens read
so far, last first. -/
def lexFrom (cs : List Char) (p : TextPos) (acc : List Token) : Except ParseError (List Token) :=
  match cs with
  | [] => .ok (⟨.eof, p⟩ :: acc).reverse
  | ' ' :: rest | '\t' :: rest => lexFrom rest (p.advance 1) acc
  | '\n' :: rest => lexFrom rest ⟨p.line + 1, 1⟩ acc
  | '/' :: '/' :: rest =>
    let body := rest.takeWhile notLineFeed
    match firstDisallowed body 0 with
    | some (c, n) => errorAt (p.advance (2 + n)) (codePoint c ++ " is not allowed outside strings")
    | none =>
      have := length_dropWhile_le notLineFeed rest
      lexFrom (rest.dropWhile notLineFeed) (p.advance (2 + utf8Len body)) acc
  | c :: rest => do
    let (t, ⟨r, _hr⟩, q) ← lexToken c rest p
    lexFrom r q (⟨t, p⟩ :: acc)
termination_by cs.length
decreasing_by all_goals (simp_wf <;> omega)

/-- The tokens of a text, ending with `eof`. -/
def lex (text : String) : Except ParseError (List Token) := lexFrom text.toList ⟨1, 1⟩ []

end Fir.Text
