import Fir.Syntax.Module

/-!
fir has one text format, and it is canonical (P3, ADR-2026-10-29-2014): one
spelling for every construct, no sugar, and a printer that is the formatter.
The text is the interface between Lean and Rust: Rust prints a module, Lean
parses and reprints it, and the bytes must match.

This chapter gives the grammar of the text in three parts: the tokens, below;
the grammar of a module, which is the same for every dialect (G0); and the
canonical printer, a Lean definition that fixes the one spelling of each
module. A parser accepts the grammar, with any whitespace and comments around
the tokens. The printer emits one layout, without comments, and `funk fmt`
prints a module in that layout.

# Characters

A text is UTF-8, and a line feed ends each of its lines. The last line need
not have one: a parser accepts a text that does not end with a line feed,
and a comment may end at the end of the text. The printer always ends a
text with a line feed.

Outside strings, a text holds none of the characters that `isEscaped` holds
for, except the tab and the line feed: no carriage return, no byte-order
mark and no bidirectional control, not even in a comment. `"` and `\` are
not among them, so a comment may hold them. A parser rejects a text that
holds one of those characters (`allowedOutsideStrings`). So a text has one
kind of line end, and it cannot show a reader an order of characters other
than the one a parser reads (the Trojan Source attack).

# Tokens

```
value     ::= '%' namechar+
label     ::= '^' namechar+
symbol    ::= '@' word | '@' string
locref    ::= '@' nat
word      ::= wordstart namechar*
wordstart ::= letter | '_'
namechar  ::= letter | digit | '_' | '.'
letter    ::= 'A'..'Z' | 'a'..'z'
digit     ::= '0'..'9'
nat       ::= '0' | ('1'..'9') digit*
int       ::= nat | '-' ('1'..'9') digit*
string    ::= '"' (strchar | escape)* '"'
strchar   ::= any character except '"', '\' and the escaped characters
escape    ::= '\\' | '\"' | '\n' | '\t' | '\u{' hexdigit+ '}'
hexdigit  ::= digit | 'a'..'f'
punct     ::= '(' | ')' | '{' | '}' | ',' | ':' | '=' | '->'
```

* A value is named `%` and one or more name characters, so `%0` and `%acc.1`
  are values. A block label is named the same way after `^`.
* A symbol names a function or another global. Its name is written after
  `@` as a word when it is one, as in `@sum`, and as a string otherwise, as
  in `@"1"` or `@"_ZN3foo$LT$E"`. A name that is a word is never quoted, so
  each name has one spelling, and a parser rejects `@"sum"`.
* A location reference is `@` and a number. `@1` is always a location
  reference: the symbol named `1` is written `@"1"`.
* A word is an op name, a type, a word attribute such as a flag, an item
  kind or a keyword. Words may
  contain `.`, which is reserved to put a dialect's name before the names of
  its ops (H4). No word of the core dialect contains one.
* An integer has no leading zeros and no `+`. A negative integer starts with
  `-`, and `-0` is not an integer. The only other token with `-` is `->`.
* Whitespace is spaces, tabs and line feeds. A comment runs from `//` to the
  end of its line, outside strings. Whitespace and comments may come before,
  between and after tokens, and the parser drops them.
* Tokens are read by maximal munch: each token is the longest one that the
  text starts with. A value, a label, a symbol written as a word, a location
  reference, a word or an integer must not be followed directly by a name
  character, so `@1x` and `1abc` are errors, while `const-1` reads as
  `const -1`.
* There is no float literal and no nested symbol reference, such as
  `@a::@b`. Floats (S5) and nested symbol references will need new tokens,
  and until they get them a dialect cannot write either. So `1.5` is an
  error: an integer followed by a name character.

# Strings

A string holds any Unicode text, and has one spelling:

* `"` and `\` are written `\"` and `\\`, a line feed `\n` and a tab `\t`.
* Each other escaped character is written `\u{h}`, where `h` is its code
  point in lowercase hexadecimal with no leading zeros. The escaped
  characters are the control characters (Unicode's category Cc: U+0000 to
  U+001F and U+007F to U+009F), the format characters (category Cf) of
  Unicode 16.0, listed in `formatChars` below, and the line and paragraph
  separators U+2028 and U+2029. The format characters include the
  bidirectional controls and the byte-order mark.
* No other character is escaped. A parser accepts `\u{h}` only for an
  escaped character other than the line feed and the tab, spelled as above:
  `\u{41}` for `A`, `\u{9}` for a tab and `\u{001}` are errors.

# Numbers

Numbers have limits, so that every implementation can hold them in integers
of a fixed width (N3). N3's bound of `2^32` covers the numbers that give the
text its structure, as the decision memo on #8 lists them: a location
reference, a line and a column are below `2^32`. An integer attribute is a
value of its dialect, not one of those numbers. It has no limit of its own:
the dialect that reads it bounds it, as a core constant must fit its type.
The core dialect bounds its widths in its own section. A parser rejects a
number out of its range, at the number.

Which strings are names and words is defined with the abstract syntax
(`isName`, `isWord`). The definitions below give the canonical spelling of
integers, strings and symbols, which the printer uses.
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

/-- The canonical spelling of an integer. -/
def printInt (i : Int) : String := toString i

/-- The canonical spelling of a symbol: `@` and its name, quoted unless the
name is a word. -/
def printSymbol (s : String) : String := "@" ++ if isWord s then s else quote s

#guard quote "a\"b\\c\n\x01é" == "\"a\\\"b\\\\c\\n\\u{1}é\""
#guard quote "\u202e\u2066\ufeff\u0085\u2028" == "\"\\u{202e}\\u{2066}\\u{feff}\\u{85}\\u{2028}\""
#guard ['"', '\\', '\t', '\n', 'é'].all allowedOutsideStrings
#guard ['\r', '\u0085', '\u200e', '\u202e', '\u2066', '\ufeff', '\u2028'].all (!allowedOutsideStrings ·)
#guard printInt (-128) == "-128" && printInt 0 == "0"
#guard isWord "icmp" && isWord "gpu.launch" && !isWord "1f" && isName "0" && !isName ""
#guard printSymbol "sum" == "@sum" && printSymbol "1" == "@\"1\"" &&
  printSymbol "a\nb" == "@\"a\\nb\"" && printSymbol "" == "@\"\""

end Fir.Text
