import Fir.Text.Lex

/-!
# The tokens of a printed module

The proof that parsing a printed module gives the module back (#11) follows
the parser's three steps. Its first step is about the lexer: the printer
writes a module as a list of tokens, each in its one spelling, with
whitespace between them, and the lexer reads exactly those tokens back
(`lex_print`, below). This section gives that list. The grammar step reads
it, and only it, into a syntax tree.

Each token has one spelling, `Tok.spell`, the one that the printer writes.
A token can be written when its name or word is one (`Tok.Writable`): a
value name or a label is a name, a word is a word, and a location reference
is below `2^32`. Every symbol, integer and string can be written. The end of
the text, `eof`, is no token of the printed text: the lexer adds it.

The tokens of each construct are listed in the order that the printer
writes them, function by function: `Attr.tokens` for `Attr.print`,
`Operation.tokens` for `Operation.print`, and so on up to `Module.tokens`.
Whitespace, indentation and line feeds have no tokens.
-/

namespace Fir.Text

/-- The one spelling of a token, as the printer writes it. The end of the
text has none. -/
def Tok.spell : Tok → String
  | .value n => "%" ++ n
  | .label n => "^" ++ n
  | .sym s => printSymbol s
  | .locRef r => printLocRef r
  | .word w => w
  | .int i => printInt i
  | .str s => quote s
  | .lparen => "(" | .rparen => ")" | .lbrace => "{" | .rbrace => "}"
  | .comma => "," | .colon => ":" | .eq => "=" | .arrow => "->"
  | .eof => ""

/-- A token that can be written: a value name or a label is a name, a word
is a word, and a location reference is below `2^32`. The end of the text is
not written. -/
def Tok.Writable : Tok → Prop
  | .value n | .label n => isName n
  | .word w => isWord w
  | .locRef r => r < Location.limit
  | .eof => False
  | _ => True

end Fir.Text

namespace Fir

open Text

/-- The tokens of an attribute, or of a type. -/
def Attr.tokens : Attr → List Tok
  | .word w => [.word w]
  | .int i => [.int i]
  | .str s => [.str s]
  | .sym s => [.sym s]
  | .app h args => .word h :: .lparen :: [Tok.comma].intercalate (tokensList args) ++ [.rparen]
where
  /-- The tokens of each attribute of a list. -/
  tokensList : List Attr → List (List Tok)
    | [] => []
    | a :: as => a.tokens :: tokensList as

/-- The tokens of a location, as the location table writes it. -/
def Location.tokens : Location → List Tok
  | .unknown => [.word "unknown"]
  | .range f l₁ c₁ l₂ c₂ =>
    [.str f, .colon, .int l₁, .colon, .int c₁, .word "to", .int l₂, .colon, .int c₂]
  | .name n => [.word "name", .lparen, .str n, .rparen]
  | .callsite callee caller =>
    [.word "callsite", .lparen, .locRef callee, .word "at", .locRef caller, .rparen]
  | .fused locs =>
    .word "fused" :: .lparen :: [Tok.comma].intercalate (locs.map ([.locRef ·])) ++ [.rparen]
  | .derived src => [.word "derived", .lparen, .locRef src, .rparen]

variable {d : Dialect} [DialectText d]

/-- The tokens of a definition, `%x: T`. -/
def defTokens (x : Name × d.Ty) : List Tok := .value x.1 :: .colon :: (tyAttr x.2).tokens

/-- The tokens of a list of definitions, separated by commas. -/
def defsTokens (xs : List (Name × d.Ty)) : List Tok := [Tok.comma].intercalate (xs.map defTokens)

/-- The tokens of a successor. -/
def Succ.tokens (s : Succ) : List Tok :=
  .label s.label ::
    if s.args.isEmpty then []
    else .lparen :: [Tok.comma].intercalate (s.args.map ([.value ·])) ++ [.rparen]

mutual
/-- The tokens of an op. -/
def Operation.tokens : Operation d → List Tok
  | ⟨results, op, operands, succs, regions, loc⟩ =>
    let lhs := if results.isEmpty then [] else defsTokens results ++ [.eq]
    let head := .word (opName op) :: (opAttrs op).flatMap Attr.tokens
    let uses := operands.map ([.value ·]) ++ succs.map Succ.tokens
    let rhs := if uses.isEmpty then head else head ++ [Tok.comma].intercalate uses
    lhs ++ rhs ++ Region.tokensList regions ++ [.locRef loc]

/-- The tokens of the regions of an op. -/
def Region.tokensList : List (Region d) → List Tok
  | [] => []
  | ⟨blocks⟩ :: rs => .lbrace :: Block.tokensList blocks ++ .rbrace :: Region.tokensList rs

/-- The tokens of blocks. -/
def Block.tokensList : List (Block d) → List Tok
  | [] => []
  | ⟨label, params, body⟩ :: bs =>
    .label label :: (if params.isEmpty then [] else .lparen :: defsTokens params ++ [.rparen]) ++
      .colon :: Operation.tokensList body ++ Block.tokensList bs

/-- The tokens of ops. -/
def Operation.tokensList : List (Operation d) → List Tok
  | [] => []
  | o :: os => o.tokens ++ Operation.tokensList os
end

/-- The tokens of a function. -/
def Func.tokens (f : Func d) : List Tok :=
  let results :=
    if f.results.isEmpty then []
    else .arrow :: [Tok.comma].intercalate (f.results.map (tyAttr · |>.tokens))
  .word "func" :: .sym f.name :: .lparen :: defsTokens f.params ++ .rparen :: results ++
    .lbrace :: Block.tokensList f.body.blocks ++ [.rbrace]

/-- The tokens of an item. -/
def Item.tokens : Item d → List Tok
  | .func f => f.tokens

/-- The tokens of the location table. -/
def LocTable.tokens (t : LocTable) : List Tok :=
  .word "locs" :: .lbrace :: t.flatMap (fun (r, l) => .locRef r :: .eq :: l.tokens) ++ [.rbrace]

/-- The tokens of a module, in the order that the printer writes them. -/
def Module.tokens (m : Module d) : List Tok :=
  m.items.flatMap Item.tokens ++ m.locs.tokens

end Fir
