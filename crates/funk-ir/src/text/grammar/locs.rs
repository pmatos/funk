//! Reads the location table (`locs` in `lean/Fir/Text/Grammar.lean`). Its
//! syntax is fixed, and its numbers are checked against their limits (N3)
//! where they stand.

use super::super::ParseError;
use super::super::lexer::Tok;
use super::Parser;
use crate::ir::{LocRef, LocTable, Location};

impl Parser<'_> {
    pub(super) fn locs(&mut self) -> Result<LocTable, ParseError> {
        self.keyword("locs")?;
        self.expect(&Tok::LBrace, "{ to open the location table")?;
        let mut table = LocTable::new();
        while let Tok::LocRef(r) = self.peek() {
            let r = *r;
            self.advance();
            self.expect(&Tok::Eq, "= after the location reference")?;
            let loc = self.location()?;
            table.insert(r, loc);
        }
        self.expect(&Tok::RBrace, "an entry, such as `@0 = unknown`, or }")?;
        Ok(table)
    }

    fn location(&mut self) -> Result<Location, ParseError> {
        if let Tok::Str(file) = self.peek().clone() {
            self.advance();
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
                self.advance();
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
                self.advance();
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
                    self.advance();
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
