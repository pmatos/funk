import FirTest.Print

/-!
Tests of the first step of #11's proof, `lex_print`: the lexer reads the
printed text of a module as exactly `Module.tokens`, then `eof`. The checks
run it on modules whose names, strings and numbers need every spelling the
printer has, and on each token's spelling alone. A module with a name that
cannot be written does not lex to its tokens, which is why `lex_print`
asks that every token can be written. Characters that the repository's
hooks keep out of files are written as Lean escapes. The last checks pin
the axioms of the theorems to Lean's standard ones.
-/

namespace FirTest

open Fir Text Core

/-- The text lexes to exactly these tokens, then `eof`. -/
def lexesTo (t : String) (ts : List Tok) : Bool :=
  match lex t with
  | .ok r => r.map (·.tok) == ts ++ [.eof]
  | .error _ => false

/-- A module's printed text lexes to its tokens. -/
def lexesToTokens {d : Dialect} [DialectText d] (m : Module d) : Bool := lexesTo m.print m.tokens

/-- A module whose symbols and strings need every escape, whose constants
are negative and longer than 64 digits, and whose location table holds
every kind of location, with references, lines and columns up to the
largest below `2^32`. -/
def tricky : Module CoreDialect where
  items := [
    .func ⟨"a\"b\\c\n\t\x00\x01\u00e9\u202e\u2028\u00ad", [("x.0", i 8)], [i 8, i 256], ⟨[
      ⟨"entry", [], [
        op [("m", i 8)] (.const 8 (-128)) [] 4294967295,
        op [("z", i 8)] (.const 8 0) [] 1,
        op [("big", i 256)] (.const 256 (BitVec.ofInt 256 (-(2 ^ 255)))) [] 2,
        op [("r", i 8)] (.call "1" [i 8] [i 8]) ["m"] 3,
        op [] .br [] 4 [⟨"exit", ["r", "big"]⟩]]⟩,
      ⟨"exit", [("a", i 8), ("b", i 256)], [op [] (.ret [i 8, i 256]) ["a", "b"] 5]⟩]⟩⟩,
    .func ⟨"_", [], [], ⟨[⟨"e", [], [op [] (.ret []) [] 0]⟩]⟩⟩]
  locs := [
    (0, .unknown),
    (1, .name "\u2028\"\\\u007f"),
    (2, .callsite 0 4294967295),
    (3, .fused []),
    (4, .fused [0, 1, 2]),
    (5, .derived 4),
    (4294967295, .range "f\t\u202e.c" 4294967295 0 1 4294967295)]

#guard lexesToTokens Example.sumModule && lexesToTokens tricky
#guard lexesToTokens (nested 3) && lexesToTokens (Module.mk (d := CoreDialect) [] [])
#guard tricky.tokens.length > 100

-- Each token's spelling lexes to the token alone.
#guard [Tok.value "0", .label "acc.1", .sym "sum", .sym "1", .sym "", .sym "a\nb", .locRef 0,
    .locRef 4294967295, .word "i32", .word "_x.y", .int 0, .int (-1), .int (10 ^ 100),
    .int (-(10 ^ 100)), .str "", .str "\"\\\n\t\x7f\u0085\u200e", .lparen, .rparen, .lbrace,
    .rbrace, .comma, .colon, .eq, .arrow].all fun t => lexesTo t.spell [t]

-- Tokens that cannot be written do not lex back: an empty value name, a
-- label that is not a name, and a location reference of `2^32`.
#guard !lexesToTokens (Module.mk (d := CoreDialect)
  [.func ⟨"f", [], [], ⟨[⟨"a b", [], [op [("", i 8)] (.const 8 0) [] 0]⟩]⟩⟩] [])
#guard !lexesTo (Tok.locRef 4294967296).spell [.locRef 4294967296]

/--
info: 'Fir.lex_print' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.lex_print

/--
info: 'Fir.Module.WellFormed.lex_print' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.Module.WellFormed.lex_print

/--
info: 'Fir.Module.Valid.lex_print' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.Module.Valid.lex_print

end FirTest
