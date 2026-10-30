//! Reads tokens by the grammar of a module (`lean/Fir/Text/Grammar.lean`).
//!
//! One grammar covers every item and every op of every dialect, so this file
//! has no code for any particular op. Location tables are read here too:
//! their syntax is fixed, and their numbers are checked against their limits
//! (N3) where they stand.

use super::lexer::{Tok, Token};
use super::syntax::{SBlock, SBody, SDef, SItem, SModule, SOp, SType};
use super::{ParseError, TextPos};
use crate::ir::{Attr, LocRef, LocTable, Location, Succ, Type};

/// Reads a module from its tokens.
pub(super) fn module(tokens: Vec<Token>) -> Result<SModule, ParseError> {
    let mut p = Parser { tokens, at: 0 };
    let mut items = Vec::new();
    loop {
        match p.peek() {
            Tok::Word(w) if w == "locs" => break,
            Tok::Word(_) => items.push(p.item()?),
            _ => return p.fail("an item or the location table, `locs { ... }`"),
        }
    }
    let locs = p.locs()?;
    p.expect(&Tok::Eof, "the end of the text after the location table")?;
    Ok(SModule { items, locs })
}

struct Parser {
    tokens: Vec<Token>,
    at: usize,
}

impl Parser {
    fn peek(&self) -> &Tok {
        &self.tokens[self.at].tok
    }

    fn pos(&self) -> TextPos {
        self.tokens[self.at].pos
    }

    fn next(&mut self) -> Token {
        let t = self.tokens[self.at].clone();
        if t.tok != Tok::Eof {
            self.at += 1;
        }
        t
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
            self.next();
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
                self.next();
                Ok((w, pos))
            }
            _ => self.fail(expected),
        }
    }

    fn keyword(&mut self, kw: &str) -> Result<(), ParseError> {
        match self.peek() {
            Tok::Word(w) if w == kw => {
                self.next();
                Ok(())
            }
            _ => self.fail(&format!("`{kw}`")),
        }
    }

    fn item(&mut self) -> Result<SItem, ParseError> {
        let (kind, kind_pos) = self.word("an item kind")?;
        let Tok::Sym(name) = self.peek().clone() else {
            return self.fail("the item's symbol");
        };
        self.next();
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
        let body = match self.peek() {
            Tok::Word(_) => {
                let mut items = Vec::new();
                while matches!(self.peek(), Tok::Word(_)) {
                    items.push(self.item()?);
                }
                SBody::Items(items)
            }
            _ => SBody::Blocks(self.blocks()?),
        };
        self.expect(&Tok::RBrace, "} to close the item's body")?;
        Ok(SItem {
            kind,
            kind_pos,
            name,
            params,
            results,
            attrs,
            body,
        })
    }

    fn defs(&mut self) -> Result<Vec<SDef>, ParseError> {
        let mut defs = vec![self.def()?];
        while self.eat(&Tok::Comma) {
            defs.push(self.def()?);
        }
        Ok(defs)
    }

    fn def(&mut self) -> Result<SDef, ParseError> {
        let pos = self.pos();
        let Tok::Value(name) = self.peek().clone() else {
            return self.fail("a value definition, `%x: type`");
        };
        self.next();
        self.expect(&Tok::Colon, ": and the value's type")?;
        Ok(SDef {
            name,
            pos,
            ty: self.ty()?,
        })
    }

    fn ty(&mut self) -> Result<SType, ParseError> {
        let (name, pos) = self.word("a type")?;
        let ty = if self.peek() == &Tok::LParen {
            Type::app(name, self.attr_args()?)
        } else {
            Type::word(name)
        };
        Ok(SType { ty, pos })
    }

    fn at_attr(&self) -> bool {
        matches!(
            self.peek(),
            Tok::Word(_) | Tok::Int(_) | Tok::Str(_) | Tok::Sym(_)
        )
    }

    fn attr(&mut self) -> Result<Attr, ParseError> {
        let attr = match self.peek().clone() {
            Tok::Word(w) => {
                self.next();
                if self.peek() == &Tok::LParen {
                    return Ok(Attr::App(w, self.attr_args()?));
                }
                Attr::Word(w)
            }
            Tok::Int(i) => Attr::Int(i),
            Tok::Str(s) => Attr::Str(s),
            Tok::Sym(s) => Attr::Sym(s),
            _ => return self.fail("an attribute"),
        };
        if !matches!(attr, Attr::Word(_)) {
            self.next();
        }
        Ok(attr)
    }

    /// `'(' attrs? ')'`, after a word.
    fn attr_args(&mut self) -> Result<Vec<Attr>, ParseError> {
        self.expect(&Tok::LParen, "(")?;
        let mut args = Vec::new();
        if !self.eat(&Tok::RParen) {
            args.push(self.attr()?);
            while self.eat(&Tok::Comma) {
                args.push(self.attr()?);
            }
            self.expect(&Tok::RParen, ", or ) in the attribute's arguments")?;
        }
        Ok(args)
    }

    fn blocks(&mut self) -> Result<Vec<SBlock>, ParseError> {
        let mut blocks = Vec::new();
        while let Tok::Label(label) = self.peek().clone() {
            self.next();
            let mut params = Vec::new();
            if self.eat(&Tok::LParen) {
                params = self.defs()?;
                self.expect(&Tok::RParen, ", or ) after the block's arguments")?;
            }
            self.expect(&Tok::Colon, ": after the block's label")?;
            let mut ops = Vec::new();
            while matches!(self.peek(), Tok::Value(_) | Tok::Word(_)) {
                ops.push(self.op()?);
            }
            blocks.push(SBlock { label, params, ops });
        }
        Ok(blocks)
    }

    fn op(&mut self) -> Result<SOp, ParseError> {
        let mut results = Vec::new();
        if matches!(self.peek(), Tok::Value(_)) {
            results = self.defs()?;
            self.expect(&Tok::Eq, "= after the op's results")?;
        }
        let (name, name_pos) = self.word("an op name")?;
        let mut attrs = Vec::new();
        while self.at_attr() {
            attrs.push(self.attr()?);
        }
        let mut operands = Vec::new();
        let mut succs = Vec::new();
        if let Tok::Value(v) = self.peek().clone() {
            operands.push((v, self.pos()));
            self.next();
            while self.eat(&Tok::Comma) {
                match self.peek().clone() {
                    Tok::Value(v) if succs.is_empty() => {
                        operands.push((v, self.pos()));
                        self.next();
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
        let mut regions = Vec::new();
        while self.eat(&Tok::LBrace) {
            regions.push(self.blocks()?);
            self.expect(&Tok::RBrace, "a block or } to close the region")?;
        }
        let loc = match self.peek() {
            Tok::LocRef(r) => *r,
            _ => return self.fail("the op's location reference, such as @0"),
        };
        self.next();
        Ok(SOp {
            results,
            name,
            name_pos,
            attrs,
            operands,
            succs,
            regions,
            loc,
        })
    }

    fn succ(&mut self) -> Result<Succ, ParseError> {
        let Tok::Label(label) = self.peek().clone() else {
            return self.fail("a successor, such as ^next");
        };
        self.next();
        let mut args = Vec::new();
        if self.eat(&Tok::LParen) {
            loop {
                let Tok::Value(v) = self.peek().clone() else {
                    return self.fail("a value passed to the successor");
                };
                self.next();
                args.push(v);
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.expect(&Tok::RParen, ", or ) after the successor's arguments")?;
        }
        Ok(Succ { label, args })
    }

    fn locs(&mut self) -> Result<LocTable, ParseError> {
        self.keyword("locs")?;
        self.expect(&Tok::LBrace, "{ to open the location table")?;
        let mut table = LocTable::new();
        while let Tok::LocRef(r) = self.peek() {
            let r = *r;
            self.next();
            self.expect(&Tok::Eq, "= after the location reference")?;
            let loc = self.location()?;
            table.insert(r, loc);
        }
        self.expect(&Tok::RBrace, "an entry, such as `@0 = unknown`, or }")?;
        Ok(table)
    }

    fn location(&mut self) -> Result<Location, ParseError> {
        if let Tok::Str(file) = self.peek().clone() {
            self.next();
            self.expect(&Tok::Colon, ": after the file")?;
            let start_line = self.nat("a line")?;
            self.expect(&Tok::Colon, ":")?;
            let start_col = self.nat("a column")?;
            self.keyword("to")?;
            let end_line = self.nat("a line")?;
            self.expect(&Tok::Colon, ":")?;
            let end_col = self.nat("a column")?;
            return Ok(Location::Range {
                file,
                start_line,
                start_col,
                end_line,
                end_col,
            });
        }
        let (kind, kind_pos) = self.word("a location")?;
        match kind.as_str() {
            "unknown" => return Ok(Location::Unknown),
            "name" | "callsite" | "fused" | "derived" => {}
            _ => {
                return Err(ParseError {
                    pos: kind_pos,
                    reason: format!("{kind} is not a kind of location"),
                });
            }
        }
        self.expect(&Tok::LParen, "(")?;
        let loc = match kind.as_str() {
            "name" => {
                let Tok::Str(n) = self.peek().clone() else {
                    return self.fail("the name, as a string");
                };
                self.next();
                Location::Name(n)
            }
            "callsite" => {
                let callee = self.locref()?;
                self.keyword("at")?;
                Location::CallSite {
                    callee,
                    caller: self.locref()?,
                }
            }
            "fused" => {
                let mut locs = Vec::new();
                if self.peek() != &Tok::RParen {
                    locs.push(self.locref()?);
                    while self.eat(&Tok::Comma) {
                        locs.push(self.locref()?);
                    }
                }
                Location::Fused(locs)
            }
            _ => Location::Derived(self.locref()?),
        };
        self.expect(&Tok::RParen, ")")?;
        Ok(loc)
    }

    fn locref(&mut self) -> Result<LocRef, ParseError> {
        match self.peek() {
            Tok::LocRef(r) => {
                let r = *r;
                self.next();
                Ok(r)
            }
            _ => self.fail("a location reference, such as @0"),
        }
    }

    /// A line or a column: a `nat` below `2^32`.
    fn nat(&mut self, what: &str) -> Result<u32, ParseError> {
        let pos = self.pos();
        match self.peek() {
            Tok::Int(i) if !i.is_negative() => match i.as_str().parse::<u32>() {
                Ok(n) => {
                    self.next();
                    Ok(n)
                }
                Err(_) => Err(ParseError {
                    pos,
                    reason: format!("{what} {i} is out of range: it must be below 2^32"),
                }),
            },
            _ => self.fail(what),
        }
    }
}
