//! Reads an item's head, through the `{` of its body (`readItem` in
//! `lean/Fir/Text/Read.lean`): its kind, its symbol, its parameters, each
//! with the attributes after its type and maybe ending in `...`, its
//! results, each with the attributes after its type, and its attributes.
//! The attributes after the last result are the item's, as the spec reads
//! them.

use super::super::ParseError;
use super::super::TextPos;
use super::super::lexer::Tok;
use super::super::syntax::{DefPos, SBody, SItem};
use super::Parser;
use crate::ir::{Attr, Def, Type};

/// The attributes after a definition or a type, each with its position.
type Attrs = Vec<(Attr, TextPos)>;

/// The parameters as read, each with its attributes, and the position of
/// the `...` that ends them, if any.
type Params = (Vec<((Def, DefPos), Attrs)>, Option<TextPos>);

impl Parser<'_> {
    /// `word symbol '(' params? ')' ('->' results)? attr* '{'`: an item up
    /// to its body.
    pub(super) fn item_head(&mut self) -> Result<SItem, ParseError> {
        let (kind, kind_pos) = self.word("an item kind")?;
        let Tok::Sym(name) = self.peek().clone() else {
            return self.fail("the item's symbol");
        };
        self.advance();
        self.expect(&Tok::LParen, "( and the item's parameters")?;
        let (params, variadic) = if self.peek() == &Tok::RParen {
            (Vec::new(), None)
        } else {
            self.params()?
        };
        self.expect(&Tok::RParen, ")")?;
        let mut results = Vec::new();
        if self.eat(&Tok::Arrow) {
            results.push(self.result()?);
            while self.eat(&Tok::Comma) {
                results.push(self.result()?);
            }
        }
        let mut attrs = self.attrs()?;
        let (params, param_attrs) = params.into_iter().unzip();
        let (results, mut result_attrs): (Vec<_>, Vec<Attrs>) = results.into_iter().unzip();
        if let Some(mut last) = result_attrs.pop() {
            last.append(&mut attrs);
            attrs = last;
        }
        self.expect(&Tok::LBrace, "{ and the item's body")?;
        Ok(SItem {
            kind,
            kind_pos,
            name,
            params,
            param_attrs,
            variadic,
            results,
            result_attrs,
            attrs,
            body: SBody::Items(Vec::new(), Vec::new()),
        })
    }

    /// `...` alone, or parameters separated by commas, which may end in
    /// `, ...`; the position of the `...`, if any.
    fn params(&mut self) -> Result<Params, ParseError> {
        let mut params = Vec::new();
        if self.peek() == &Tok::Ellipsis {
            let pos = self.pos();
            self.advance();
            return Ok((params, Some(pos)));
        }
        loop {
            let def = self.def()?;
            params.push((def, self.attrs()?));
            if !self.eat(&Tok::Comma) {
                return Ok((params, None));
            }
            if self.peek() == &Tok::Ellipsis {
                let pos = self.pos();
                self.advance();
                return Ok((params, Some(pos)));
            }
        }
    }

    /// A result: a type, then its attributes.
    fn result(&mut self) -> Result<((Type, TextPos), Attrs), ParseError> {
        let ty = self.ty()?;
        Ok((ty, self.attrs()?))
    }

    /// The attributes that start here, each with its position.
    fn attrs(&mut self) -> Result<Attrs, ParseError> {
        let mut attrs = Vec::new();
        while self.at_attr() {
            let pos = self.pos();
            attrs.push((self.attr()?, pos));
        }
        Ok(attrs)
    }
}
