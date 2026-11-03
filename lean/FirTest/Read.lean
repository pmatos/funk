import Fir.Text.ReadModule
import FirTest.Lex

/-!
Tests of the grammar step of #11's proof, `readModule_tokens`: on a
module's tokens, then `eof`, at any positions, `readModule` gives the
module's tree once its positions are erased. The checks read the tokens
that the lexer gives for the printed text, and the same tokens at made-up
positions. They cover modules of the core dialect and of a dialect whose
ops and types are any attributes, so that applied attributes and types
(`h()` is not `h`), successors and regions are read too. A function with no
blocks reads with the body `SBody.blocks []`. A type written as an integer,
and a line of `2^32`, do not read back, which is why `readModule_tokens`
asks that types are written as types and that the location table is within
the limits. Trees have no `BEq` instance, since a derived one would be
`partial` (ADR-2026-10-30-1452), so the checks compare them with the
structural functions below. The last checks pin the axioms of the theorems
to Lean's standard ones.
-/

namespace FirTest

open Fir Text

/-! # Comparing trees -/

mutual
/-- Two attributes are the same. -/
def attrEq : Attr → Attr → Bool
  | .word a, .word b | .str a, .str b | .sym a, .sym b => a == b
  | .int a, .int b => a == b
  | .app h as, .app h' bs => h == h' && attrsEq as bs
  | _, _ => false

/-- Two lists of attributes are the same. -/
def attrsEq : List Attr → List Attr → Bool
  | [], [] => true
  | a :: as, b :: bs => attrEq a b && attrsEq as bs
  | _, _ => false
end

/-- Two lists are the same, by `eq` on their elements. -/
def listEq {α : Type} (eq : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => eq a b && listEq eq as bs
  | _, _ => false

/-- Two definitions are the same, positions included. -/
def sdefEq (x y : SDef) : Bool :=
  x.name == y.name && x.pos == y.pos && attrEq x.ty y.ty && x.tyPos == y.tyPos

/-- Two attributes at their positions are the same. -/
def atEq (x y : Attr × TextPos) : Bool := attrEq x.1 y.1 && x.2 == y.2

mutual
/-- Two ops are the same, at any depth. -/
def sopEq : SOp → SOp → Bool
  | ⟨r, n, np, a, o, s, rs, l⟩, ⟨r', n', np', a', o', s', rs', l'⟩ =>
    listEq sdefEq r r' && n == n' && np == np' && attrsEq a a' && o == o' && s == s' &&
      regionsEq rs rs' && l == l'

/-- Two lists of regions are the same. -/
def regionsEq : List SRegion → List SRegion → Bool
  | [], [] => true
  | ⟨bs⟩ :: rs, ⟨bs'⟩ :: rs' => blocksEq bs bs' && regionsEq rs rs'
  | _, _ => false

/-- Two lists of blocks are the same. -/
def blocksEq : List SBlock → List SBlock → Bool
  | [], [] => true
  | ⟨l, ps, os⟩ :: bs, ⟨l', ps', os'⟩ :: bs' =>
    l == l' && listEq sdefEq ps ps' && opsEq os os' && blocksEq bs bs'
  | _, _ => false

/-- Two lists of ops are the same. -/
def opsEq : List SOp → List SOp → Bool
  | [], [] => true
  | o :: os, o' :: os' => sopEq o o' && opsEq os os'
  | _, _ => false
end

mutual
/-- Two items are the same, at any depth. -/
def sitemEq : SItem → SItem → Bool
  | ⟨k, kp, n, ps, rs, as, b⟩, ⟨k', kp', n', ps', rs', as', b'⟩ =>
    k == k' && kp == kp' && n == n' && listEq sdefEq ps ps' && listEq atEq rs rs' &&
      listEq atEq as as' && sbodyEq b b'

/-- Two item bodies are the same. -/
def sbodyEq : SBody → SBody → Bool
  | .blocks bs, .blocks bs' => blocksEq bs bs'
  | .items is, .items is' => sitemsEq is is'
  | _, _ => false

/-- Two lists of items are the same. -/
def sitemsEq : List SItem → List SItem → Bool
  | [], [] => true
  | i :: is, i' :: is' => sitemEq i i' && sitemsEq is is'
  | _, _ => false
end

/-- Two module trees are the same. -/
def smoduleEq (s s' : SModule) : Bool := sitemsEq s.items s'.items && s.locs == s'.locs

/-! # Reading the tokens of a module -/

/-- The printed text of `m` reads, through the lexer and the grammar, as
`m`'s tree. -/
def readsPrinted {d : Dialect} [DialectText d] (m : Module d) : Bool :=
  match lex m.print with
  | .ok ts =>
    match readModule ts with
    | .ok s => smoduleEq s.erase m.tree
    | .error _ => false
  | .error _ => false

/-- The tokens of `m` at made-up positions. -/
def tokensAt {d : Dialect} [DialectText d] (m : Module d) : List Token :=
  (m.tokens ++ [Tok.eof]).zipIdx.map fun (t, i) => ⟨t, ⟨i % 7, 3 * i⟩⟩

/-- The tokens of `m`, then `eof`, at made-up positions read as `m`'s
tree. -/
def readsTokensAt {d : Dialect} [DialectText d] (m : Module d) : Bool :=
  match readModule (tokensAt m) with
  | .ok s => smoduleEq s.erase m.tree
  | .error _ => false

/-- A dialect whose op instances are a name and attributes, and whose types
are attributes, each written as it is. -/
abbrev AttrDialect : Dialect := ⟨String × List Attr, Attr⟩

instance : DialectText AttrDialect where
  opName o := o.1
  opAttrs o := o.2
  decodeOp n as _ _ := some (n, as)
  tyAttr t := t
  decodeTy a := some a

/-- An op of `AttrDialect`. -/
def aop (results : List (Name × Attr)) (name : String) (attrs : List Attr)
    (operands : List Name) (succs : List Succ := []) (regions : List (Region AttrDialect) := [])
    (loc : LocRef := 0) : Operation AttrDialect :=
  ⟨results, (name, attrs), operands, succs, regions, loc⟩

/-- A module whose types and attributes are applied words with and without
arguments, whose ops have successors with and without arguments and
regions with and without blocks, and whose last function has no blocks. -/
def applied : Module AttrDialect where
  items := [
    .func ⟨"g", [("x", .app "h" []), ("y", .word "h")], [.app "vec" [.int 4, .word "i32"], .word "h"],
      ⟨[⟨"entry", [], [
          aop [("r", .app "h" [.app "h" [], .str "s\"", .sym "1", .int (-3)])] "op.a"
            [.app "h" [], .word "h", .int 7, .str "", .sym "f", .app "k" [.word "h"]] ["x", "y"]
            [⟨"b", ["x", "y"]⟩, ⟨"c", []⟩]
            [⟨[⟨"in", [("z", .word "t"), ("w", .app "t" [])],
                [aop [] "yield" [] ["z"] [] [] 1]⟩]⟩, ⟨[]⟩],
          aop [] "ret" [] [] [] [⟨[]⟩] 2]⟩,
        ⟨"b", [("q", .word "h"), ("q2", .app "h" [])], [aop [] "ret" [] ["q"] [] [] 2]⟩,
        ⟨"c", [], [aop [("u", .word "a"), ("v", .app "b" [])] "pair" [] [],
          aop [] "ret" [.word "h"] ["u", "v"] [] [] 3]⟩]⟩⟩,
    .func ⟨"empty", [], [], ⟨[]⟩⟩,
    .func ⟨"1", [("p", .word "h")], [], ⟨[⟨"e", [], [aop [] "br" [] [] [⟨"e", []⟩]]⟩]⟩⟩]
  locs := [(0, .unknown), (1, .range "f.c" 1 0 4294967295 4), (2, .fused []),
    (3, .fused [0, 1, 2]), (4, .callsite 1 2), (5, .derived 4), (6, .name "n")]

#guard readsPrinted Example.sumModule && readsTokensAt Example.sumModule
#guard readsPrinted tricky && readsTokensAt tricky
#guard readsPrinted (nested 3) && readsTokensAt (nested 3)
#guard readsPrinted (Module.mk (d := CoreDialect) [] []) &&
  readsTokensAt (Module.mk (d := CoreDialect) [] [])
#guard readsPrinted applied && readsTokensAt applied

-- The tree keeps the positions of the tokens: erasing them changes it.
#guard match readModule (tokensAt applied) with
  | .ok s => !smoduleEq s s.erase
  | .error _ => false

-- A function with no blocks, `{ }`, reads as a body of no blocks.
#guard match readModule (tokensAt applied) with
  | .ok ⟨[_, ⟨_, _, "empty", [], [], [], .blocks []⟩, _], _⟩ => true
  | _ => false

-- A type that is not written as a type does not read back, and neither
-- does a line of `2^32`.
#guard !readsTokensAt (Module.mk (d := AttrDialect)
  [.func ⟨"f", [("x", .int 5)], [], ⟨[]⟩⟩] [])
#guard !readsTokensAt (Module.mk (d := AttrDialect)
  [.func ⟨"f", [], [.str "t"], ⟨[]⟩⟩] [])
#guard !readsTokensAt (Module.mk (d := AttrDialect) [] [(0, .range "f" 4294967296 1 1 1)])

/--
info: 'Fir.readModule_tokens' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.readModule_tokens

/--
info: 'Fir.Module.WellFormed.readModule_tokens' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.Module.WellFormed.readModule_tokens

/--
info: 'Fir.Module.WellFormed.read_print' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.Module.WellFormed.read_print

/--
info: 'Fir.Module.Valid.read_print' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.Module.Valid.read_print

end FirTest
