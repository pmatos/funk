/-!
fir has one text format, and it is canonical (P3, ADR-2026-10-29-2014): one
spelling for every construct, no sugar, and a printer that is the formatter.
The text is the interface between Lean and Rust: Rust prints a module, Lean
parses and reprints it, and the bytes must match.

This chapter gives the grammar of the text in three parts: the tokens, below;
the grammar of a module, which is the same for every dialect (G0); and the
canonical printer, a Lean definition that fixes the one spelling of each
module. A parser accepts the grammar, with any whitespace between tokens and
with comments. The printer emits one layout, without comments, and
`funk fmt` prints a module in that layout.

# Tokens

```
value    ::= '%' namechar+
label    ::= '^' namechar+
symbol   ::= '@' wordstart namechar*
locref   ::= '@' nat
word     ::= wordstart namechar*
wordstart ::= letter | '_'
namechar ::= letter | digit | '_' | '.'
letter   ::= 'A'..'Z' | 'a'..'z'
digit    ::= '0'..'9'
nat      ::= '0' | ('1'..'9') digit*
int      ::= nat | '-' ('1'..'9') digit*
string   ::= '"' (strchar | escape)* '"'
escape   ::= '\\' | '\"' | '\n' | '\t' | '\u{' hexdigit+ '}'
punct    ::= '(' | ')' | '{' | '}' | ',' | ':' | '=' | '-' | '->'
```

* A value is named `%` and one or more name characters, so `%0` and `%acc.1`
  are values. A block label is named the same way after `^`.
* A symbol starts with a letter or `_`, so `@` followed by a digit is always
  a location reference: `@sum` is a symbol and `@1` a location reference.
* A word is an op name, a type, a flag or a keyword. Words may contain `.`,
  as in `icmp.slt`.
* An integer has no leading zeros and no `+`. A negative integer starts with
  `-`, and `-0` is not an integer.
* A string holds any Unicode text. Inside it, `"` and `\` are written `\"`
  and `\\`, a line feed `\n` and a tab `\t`. Every other control character,
  below U+0020 or U+007F, is written `\u{h}` with lowercase hexadecimal
  digits and no leading zeros. Nothing else is escaped.
* Whitespace is spaces, tabs and line feeds. A comment runs from `//` to the
  end of its line, outside strings. Both may appear between any two tokens,
  and whitespace must separate two tokens that would otherwise run together.
  The parser drops comments, so a printed module has none.

The definitions below give the canonical spelling of names, integers and
strings, which the printer uses.
-/

namespace Fir.Text

/-- An ASCII letter. -/
def isLetter (c : Char) : Bool := ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z')

/-- A character that may start a word or a symbol. -/
def isWordStart (c : Char) : Bool := isLetter c ∨ c = '_'

/-- A character of a name: a letter, a digit, `_` or `.`. -/
def isNameChar (c : Char) : Bool := isWordStart c ∨ c.isDigit ∨ c = '.'

/-- A valid value name or block label, without its sigil. -/
def isName (s : String) : Bool := !s.isEmpty && s.all isNameChar

/-- A valid word, or symbol without its `@`. -/
def isWord (s : String) : Bool :=
  match s.toList with
  | c :: cs => isWordStart c && cs.all isNameChar
  | [] => false

/-- The lowercase hexadecimal digits of `n`, with no leading zeros. -/
def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- The canonical spelling of one character inside a string. -/
def escapeChar (c : Char) : String :=
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if c = '\n' then "\\n"
  else if c = '\t' then "\\t"
  else if c.toNat < 0x20 ∨ c.toNat = 0x7f then "\\u{" ++ hex c.toNat ++ "}"
  else c.toString

/-- The canonical spelling of a string, with its quotes. -/
def quote (s : String) : String :=
  "\"" ++ String.join (s.toList.map escapeChar) ++ "\""

/-- The canonical spelling of an integer. -/
def printInt (i : Int) : String := toString i

#guard quote "a\"b\\c\n\x01é" == "\"a\\\"b\\\\c\\n\\u{1}é\""
#guard printInt (-128) == "-128" && printInt 0 == "0"
#guard isWord "icmp.slt" && !isWord "1f" && isName "0" && !isName ""

end Fir.Text
