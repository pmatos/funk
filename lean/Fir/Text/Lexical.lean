import Fir.Syntax.Module

/-!
fir has one text format, and it is canonical (ADR-2026-10-29-2014): one
spelling for every construct, no sugar, and a printer that is the formatter.
The text is the interface between Lean and Rust: Rust prints a module, Lean
parses and reprints it, and the bytes must match.

The chapter gives the text in three parts: its tokens, in this section; the
grammar of a module, which is the same for every dialect
(ADR-2026-10-29-2016); and the canonical printer, which fixes the one
spelling of each module. A parser accepts the grammar with any whitespace
and comments around the tokens. The printer writes one layout, without
comments, and `funk fmt` prints a module in that layout.

This section gives, in order: the characters that a text may hold, the one
spelling of a string, the tokens with the one spelling of an integer and of
a symbol, and what may stand between tokens.

# Characters

A text is UTF-8, and a line feed ends each of its lines. The last line need
not have one: a parser accepts a text that does not end with a line feed,
and a comment may end at the end of the text. The printer always ends a
text with a line feed. Outside strings, comments included, a text holds
only the characters defined next.
-/

namespace Fir.Text

/-- The lowercase hexadecimal digits of `n`, with no leading zeros. -/
def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- The format characters (category Cf) of Unicode 16.0, as ranges of code
points, first and last included. -/
def formatChars : List (Nat × Nat) :=
  [(0xad, 0xad), (0x600, 0x605), (0x61c, 0x61c), (0x6dd, 0x6dd), (0x70f, 0x70f),
   (0x890, 0x891), (0x8e2, 0x8e2), (0x180e, 0x180e), (0x200b, 0x200f),
   (0x202a, 0x202e), (0x2060, 0x2064), (0x2066, 0x206f), (0xfeff, 0xfeff),
   (0xfff9, 0xfffb), (0x110bd, 0x110bd), (0x110cd, 0x110cd), (0x13430, 0x1343f),
   (0x1bca0, 0x1bca3), (0x1d173, 0x1d17a), (0xe0001, 0xe0001), (0xe0020, 0xe007f)]

/-- A character that a string escapes: a control character, a format
character, or a line or paragraph separator. -/
def isEscaped (c : Char) : Bool :=
  let n := c.toNat
  n < 0x20 || (0x7f ≤ n && n ≤ 0x9f) || n == 0x2028 || n == 0x2029 ||
    formatChars.any fun (a, b) => a ≤ n && n ≤ b

/-- A character that a text may hold outside strings, comments included: the
tab, the line feed, and any character for which `isEscaped` is false (so `"`
and `\` are allowed). -/
def allowedOutsideStrings (c : Char) : Bool :=
  c = '\t' || c = '\n' || !isEscaped c

/-!
# Strings

A string holds any Unicode text, and has one spelling.
-/

/-- The canonical spelling of one character inside a string. -/
def escapeChar (c : Char) : String :=
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if c = '\n' then "\\n"
  else if c = '\t' then "\\t"
  else if isEscaped c then "\\u{" ++ hex c.toNat ++ "}"
  else c.toString

/-- The canonical spelling of a string, with its quotes. -/
def quote (s : String) : String :=
  "\"" ++ String.join (s.toList.map escapeChar) ++ "\""

/-!
# Tokens

A text is a sequence of tokens: names of values, labels and symbols,
location references, words, integers, strings and punctuation.
-/

/-- The canonical spelling of an integer. -/
def printInt (i : Int) : String := toString i

/-- The canonical spelling of a symbol: `@` and its name, quoted unless the
name is a word. -/
def printSymbol (s : String) : String := "@" ++ if isWord s then s else quote s

/-!
# Between tokens

Whitespace is spaces, tabs and line feeds. A comment runs from `//` to the
end of its line, outside strings. Whitespace and comments may come before,
between and after tokens, and the parser drops them.

Tokens are read by maximal munch: each token is the longest one that the
text starts with. A value, a label, a symbol written as a word, a location
reference, a word or an integer must not be followed directly by a name
character, so `@1x` and `1abc` are errors, while `const-1` reads as
`const -1`.

There is no float literal and no nested symbol reference, such as
`@a::@b`. Both are left to later decisions, and will need new tokens;
until they get them, a dialect cannot write either. So `1.5` is an error:
an integer followed by a name character.
-/

#guard quote "a\"b\\c\n\x01é" == "\"a\\\"b\\\\c\\n\\u{1}é\""
#guard quote "\u202e\u2066\ufeff\u0085\u2028" == "\"\\u{202e}\\u{2066}\\u{feff}\\u{85}\\u{2028}\""
#guard ['"', '\\', '\t', '\n', 'é'].all allowedOutsideStrings
#guard ['\r', '\u0085', '\u200e', '\u202e', '\u2066', '\ufeff', '\u2028'].all (!allowedOutsideStrings ·)
#guard printInt (-128) == "-128" && printInt 0 == "0"
#guard isWord "icmp" && isWord "gpu.launch" && !isWord "1f" && isName "0" && !isName ""
#guard printSymbol "sum" == "@sum" && printSymbol "1" == "@\"1\"" &&
  printSymbol "a\nb" == "@\"a\\nb\"" && printSymbol "" == "@\"\""

end Fir.Text
