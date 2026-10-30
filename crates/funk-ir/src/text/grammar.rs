//! Reads a text by the grammar of a module (`lean/Fir/Text/Grammar.lean`).
//!
//! One grammar covers every item and every op of every dialect, so this file
//! has no code for any particular op. The location table is read in
//! `grammar/locs.rs`.
//!
//! Items, regions and the arguments of attributes nest to any depth
//! (ADR-2026-10-30-1333), so none of them is read by a recursive call: the
//! lists that enclose the one being read wait in a [`Nest`]. Lists that can
//! nest start with room for one element, and an op makes room for a region
//! only when one opens, so that neither a deep nest of lists of one nor a
//! flat body takes spare room.

mod locs;

use super::lexer::{Lexer, Tok, Token};
use super::syntax::{BodyPos, DefPos, SBody, SItem, SModule};
use super::{ParseError, TextPos};
use crate::ir::tree::Nest;
use crate::ir::{Attr, Block, Def, LocRef, Op, Succ, Type};

/// Reads a module from its text.
///
/// The tokens are read as the grammar needs them. A text with an error in
/// its characters or tokens is rejected there, before any error of the
/// grammar (ADR-2026-10-30-1032), so when the grammar fails, the rest of the
/// text is still read for such an error.
pub(super) fn module(text: &str) -> Result<SModule, ParseError> {
    let mut p = Parser::new(text);
    let read = p.module();
    p.finish_tokens()?;
    read
}

struct Parser<'t> {
    lexer: Lexer<'t>,
    current: Token,
    /// The error in the characters or tokens, once the lexer meets it. The
    /// current token is then [`Tok::Eof`], so the grammar stops.
    lex_error: Option<ParseError>,
}

/// The first token of an attribute: one with no arguments, or a word
/// applied to arguments, whose `(` is read.
enum AttrHead {
    Leaf(Attr),
    App(String),
}

impl<'t> Parser<'t> {
    fn new(text: &'t str) -> Parser<'t> {
        let mut lexer = Lexer::new(text);
        let (current, lex_error) = read_token(&mut lexer);
        Parser {
            lexer,
            current,
            lex_error,
        }
    }

    fn module(&mut self) -> Result<SModule, ParseError> {
        let mut items = Vec::new();
        loop {
            match self.peek() {
                Tok::Word(w) if w == "locs" => break,
                Tok::Word(_) => items.push(self.item()?),
                _ => return self.fail("an item or the location table, `locs { ... }`"),
            }
        }
        let locs = self.locs()?;
        self.expect(&Tok::Eof, "the end of the text after the location table")?;
        Ok(SModule { items, locs })
    }

    /// Reads the rest of the text, and returns its first error in the
    /// characters or tokens, if any.
    fn finish_tokens(&mut self) -> Result<(), ParseError> {
        while self.lex_error.is_none() && self.current.tok != Tok::Eof {
            (self.current, self.lex_error) = read_token(&mut self.lexer);
        }
        match self.lex_error.take() {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }

    fn peek(&self) -> &Tok {
        &self.current.tok
    }

    fn pos(&self) -> TextPos {
        self.current.pos
    }

    /// Moves past the current token; the end of the text stays current.
    fn advance(&mut self) {
        if self.current.tok != Tok::Eof {
            (self.current, self.lex_error) = read_token(&mut self.lexer);
        }
    }

    fn fail<T>(&self, expected: &str) -> Result<T, ParseError> {
        Err(ParseError {
            pos: self.pos(),
            reason: format!("expected {expected}, found {}", self.peek().describe()),
        })
    }

    fn eat(&mut self, tok: &Tok) -> bool {
        let found = self.peek() == tok;
        if found {
            self.advance();
        }
        found
    }

    fn expect(&mut self, tok: &Tok, expected: &str) -> Result<(), ParseError> {
        if self.eat(tok) {
            Ok(())
        } else {
            self.fail(expected)
        }
    }

    fn word(&mut self, expected: &str) -> Result<(String, TextPos), ParseError> {
        let pos = self.pos();
        match self.peek() {
            Tok::Word(w) => {
                let w = w.clone();
                self.advance();
                Ok((w, pos))
            }
            _ => self.fail(expected),
        }
    }

    fn keyword(&mut self, kw: &str) -> Result<(), ParseError> {
        match self.peek() {
            Tok::Word(w) if w == kw => {
                self.advance();
                Ok(())
            }
            _ => self.fail(&format!("`{kw}`")),
        }
    }

    /// An item, with the items of its body at any depth: the bodies being
    /// read wait in a [`Nest`].
    fn item(&mut self) -> Result<SItem, ParseError> {
        let mut items = Nest::new(1);
        loop {
            items.push(self.item_head()?);
            if matches!(self.peek(), Tok::Word(_)) {
                items.open(1);
                continue;
            }
            let mut at = BodyPos::default();
            let blocks = self.blocks(&mut at)?;
            items.last_mut().expect("the item just read").body = SBody::Blocks(blocks, at);
            self.expect(&Tok::RBrace, "} to close the item's body")?;
            // The item is whole: close each body that it ends.
            loop {
                if items.is_outermost() {
                    return Ok(items.finish().pop().expect("the item just read"));
                }
                if matches!(self.peek(), Tok::Word(_)) {
                    break;
                }
                self.expect(&Tok::RBrace, "} to close the item's body")?;
                let (body, owner) = items.close().expect("an inner body");
                owner.body = SBody::Items(body);
            }
        }
    }

    /// `word symbol '(' defs? ')' ('->' types)? attr* '{'`: an item up to
    /// its body.
    fn item_head(&mut self) -> Result<SItem, ParseError> {
        let (kind, kind_pos) = self.word("an item kind")?;
        let Tok::Sym(name) = self.peek().clone() else {
            return self.fail("the item's symbol");
        };
        self.advance();
        self.expect(&Tok::LParen, "( and the item's parameters")?;
        let params = if self.peek() == &Tok::RParen {
            Vec::new()
        } else {
            self.defs()?
        };
        self.expect(&Tok::RParen, ")")?;
        let mut results = Vec::new();
        if self.eat(&Tok::Arrow) {
            results.push(self.ty()?);
            while self.eat(&Tok::Comma) {
                results.push(self.ty()?);
            }
        }
        let mut attrs = Vec::new();
        while self.at_attr() {
            let pos = self.pos();
            attrs.push((self.attr()?, pos));
        }
        self.expect(&Tok::LBrace, "{ and the item's body")?;
        Ok(SItem {
            kind,
            kind_pos,
            name,
            params,
            results,
            attrs,
            body: SBody::Items(Vec::new()),
        })
    }

    fn defs(&mut self) -> Result<Vec<(Def, DefPos)>, ParseError> {
        let mut defs = vec![self.def()?];
        while self.eat(&Tok::Comma) {
            defs.push(self.def()?);
        }
        Ok(defs)
    }

    fn def(&mut self) -> Result<(Def, DefPos), ParseError> {
        let pos = self.pos();
        let Tok::Value(name) = self.peek().clone() else {
            return self.fail("a value definition, `%x: type`");
        };
        self.advance();
        self.expect(&Tok::Colon, ": and the value's type")?;
        let (ty, ty_pos) = self.ty()?;
        let at = DefPos {
            name: pos,
            ty: ty_pos,
        };
        Ok((Def { name, ty }, at))
    }

    /// The definitions of a block's arguments or an op's results, whose
    /// positions go to `at`, in a list with no spare room.
    fn body_defs(&mut self, at: &mut BodyPos) -> Result<Vec<Def>, ParseError> {
        let pairs = self.defs()?;
        let mut defs = Vec::with_capacity(pairs.len());
        for (def, pos) in pairs {
            defs.push(def);
            at.defs.push(pos);
        }
        Ok(defs)
    }

    fn ty(&mut self) -> Result<(Type, TextPos), ParseError> {
        let (name, pos) = self.word("a type")?;
        let ty = if self.eat(&Tok::LParen) {
            Type::app(name, self.args()?)
        } else {
            Type::word(name)
        };
        Ok((ty, pos))
    }

    fn at_attr(&self) -> bool {
        matches!(
            self.peek(),
            Tok::Word(_) | Tok::Int(_) | Tok::Str(_) | Tok::Sym(_)
        )
    }

    fn attr(&mut self) -> Result<Attr, ParseError> {
        Ok(match self.attr_head()? {
            AttrHead::Leaf(a) => a,
            AttrHead::App(w) => Attr::App(w, self.args()?),
        })
    }

    fn attr_head(&mut self) -> Result<AttrHead, ParseError> {
        let leaf = match self.peek().clone() {
            Tok::Word(w) => {
                self.advance();
                return Ok(if self.eat(&Tok::LParen) {
                    AttrHead::App(w)
                } else {
                    AttrHead::Leaf(Attr::Word(w))
                });
            }
            Tok::Int(i) => Attr::Int(i),
            Tok::Str(s) => Attr::Str(s),
            Tok::Sym(s) => Attr::Sym(s),
            _ => return self.fail("an attribute"),
        };
        self.advance();
        Ok(AttrHead::Leaf(leaf))
    }

    /// `attrs? ')'`, after a word and its `(`: the arguments, with those of
    /// the applied words among them at any depth, whose lists wait in a
    /// [`Nest`].
    fn args(&mut self) -> Result<Vec<Attr>, ParseError> {
        if self.eat(&Tok::RParen) {
            return Ok(Vec::new());
        }
        let mut args = Nest::new(1);
        loop {
            match self.attr_head()? {
                AttrHead::Leaf(a) => args.push(a),
                AttrHead::App(w) => {
                    args.push(Attr::App(w, Vec::new()));
                    if !self.eat(&Tok::RParen) {
                        args.open(1);
                        continue;
                    }
                }
            }
            // The attribute is whole: close each list of arguments it ends.
            loop {
                if self.eat(&Tok::Comma) {
                    break;
                }
                self.expect(&Tok::RParen, ", or ) in the attribute's arguments")?;
                if !args.close_app() {
                    return Ok(args.finish());
                }
            }
        }
    }

    /// `block*`, read straight into the IR: a body's blocks, with the blocks
    /// of their ops' regions at any depth, which wait in a [`Nest`]. The
    /// positions that decoding reports go to `at`.
    fn blocks(&mut self, at: &mut BodyPos) -> Result<Vec<Block>, ParseError> {
        let mut blocks = Nest::new(1);
        loop {
            match self.peek() {
                Tok::Label(label) => {
                    let label = label.clone();
                    self.advance();
                    let block = self.block(label, at)?;
                    blocks.push(block);
                }
                Tok::Value(_) | Tok::Word(_) if !blocks.is_empty() => {
                    let op = self.op_head(at)?;
                    blocks.push_op(op);
                    self.op_tail(&mut blocks)?;
                }
                _ if blocks.is_outermost() => return Ok(blocks.finish()),
                _ => {
                    self.expect(&Tok::RBrace, "a block or } to close the region")?;
                    blocks.close_region();
                    self.op_tail(&mut blocks)?;
                }
            }
        }
    }

    /// `label ('(' defs ')')? ':'`, after the label: a block without its
    /// ops.
    fn block(&mut self, label: String, at: &mut BodyPos) -> Result<Block, ParseError> {
        let mut params = Vec::new();
        if self.eat(&Tok::LParen) {
            params = self.body_defs(at)?;
            self.expect(&Tok::RParen, ", or ) after the block's arguments")?;
        }
        self.expect(&Tok::Colon, ": after the block's label")?;
        Ok(Block {
            label,
            params,
            ops: Vec::with_capacity(1),
        })
    }

    /// `(defs '=')? word attr* operands?`: an op up to its regions.
    fn op_head(&mut self, at: &mut BodyPos) -> Result<Op, ParseError> {
        let mut results = Vec::new();
        if matches!(self.peek(), Tok::Value(_)) {
            results = self.body_defs(at)?;
            self.expect(&Tok::Eq, "= after the op's results")?;
        }
        let (name, name_pos) = self.word("an op name")?;
        at.ops.push(name_pos);
        let mut attrs = Vec::new();
        while self.at_attr() {
            attrs.push(self.attr()?);
        }
        let mut operands = Vec::new();
        let mut succs = Vec::new();
        if let Tok::Value(v) = self.peek().clone() {
            at.operands.push(self.pos());
            operands.push(v);
            self.advance();
            while self.eat(&Tok::Comma) {
                match self.peek().clone() {
                    Tok::Value(v) if succs.is_empty() => {
                        at.operands.push(self.pos());
                        operands.push(v);
                        self.advance();
                    }
                    _ => succs.push(self.succ()?),
                }
            }
        } else if matches!(self.peek(), Tok::Label(_)) {
            succs.push(self.succ()?);
            while self.eat(&Tok::Comma) {
                succs.push(self.succ()?);
            }
        }
        Ok(Op {
            results,
            name,
            attrs,
            operands,
            succs,
            regions: Vec::new(),
            loc: LocRef(0),
        })
    }

    /// `region* locref`, one step at a time, for the last op read: opens its
    /// next region, or ends it with its location reference.
    fn op_tail(&mut self, blocks: &mut Nest<Block>) -> Result<(), ParseError> {
        if self.eat(&Tok::LBrace) {
            blocks.last_op().regions.reserve_exact(1);
            blocks.open(1);
            return Ok(());
        }
        let loc = match self.peek() {
            Tok::LocRef(r) => *r,
            _ => return self.fail("the op's location reference, such as @0"),
        };
        self.advance();
        blocks.last_op().loc = loc;
        Ok(())
    }

    fn succ(&mut self) -> Result<Succ, ParseError> {
        let Tok::Label(label) = self.peek().clone() else {
            return self.fail("a successor, such as ^next");
        };
        self.advance();
        let mut args = Vec::new();
        if self.eat(&Tok::LParen) {
            loop {
                let Tok::Value(v) = self.peek().clone() else {
                    return self.fail("a value passed to the successor");
                };
                self.advance();
                args.push(v);
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.expect(&Tok::RParen, ", or ) after the successor's arguments")?;
        }
        Ok(Succ { label, args })
    }
}

/// The next token, or the end of the text with the error that stops the
/// lexer.
fn read_token(lexer: &mut Lexer<'_>) -> (Token, Option<ParseError>) {
    match lexer.next_token() {
        Ok(t) => (t, None),
        Err(e) => (
            Token {
                tok: Tok::Eof,
                pos: e.pos,
            },
            Some(e),
        ),
    }
}

#[cfg(test)]
mod tests {
    use crate::{Registry, parse};

    /// The lists of results and regions that the parser fills hold no
    /// spare room, as a module has one of each per op.
    #[test]
    fn parsed_lists_hold_no_spare_room() {
        let text = "func @f() {\n^e:\n  %v: i8 = const 1 @0\n  ret {\n  ^r:\n    \
                    ret %v @0\n  } @0\n}\n\nlocs {\n  @0 = unknown\n}\n";
        let m = parse(text, &Registry::core()).expect("the text parses");
        let f = m.items[0].as_func().expect("a function");
        let [def, owner] = &f.body.blocks[0].ops[..] else {
            panic!("two ops");
        };
        assert_eq!((def.results.len(), def.results.capacity()), (1, 1));
        assert_eq!(def.regions.capacity(), 0);
        assert_eq!((owner.regions.len(), owner.regions.capacity()), (1, 1));
        assert_eq!(owner.regions[0].blocks[0].ops[0].regions.capacity(), 0);
    }
}
