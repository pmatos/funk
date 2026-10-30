//! The generic syntax tree: a text read by the grammar of
//! `lean/Fir/Text/Grammar.lean`, before anything is decoded.
//!
//! It has no node for any particular op or kind of item, and it keeps the
//! position of each part that decoding can reject: a kind, an attribute, a
//! type, a definition, an op's name and each operand.

use super::TextPos;
use crate::ir::{Attr, LocRef, LocTable, Succ, Type};

/// `item ::= word symbol '(' defs? ')' ('->' types)? attr* '{' body '}'`.
#[derive(Debug)]
pub(super) struct SItem {
    pub kind: String,
    pub kind_pos: TextPos,
    pub name: String,
    pub params: Vec<SDef>,
    pub results: Vec<SType>,
    pub attrs: Vec<(Attr, TextPos)>,
    pub body: SBody,
}

/// `body ::= block* | item*`. An empty body is an empty list of blocks.
#[derive(Debug)]
pub(super) enum SBody {
    Blocks(Vec<SBlock>),
    Items(Vec<SItem>),
}

/// `block ::= label ('(' defs ')')? ':' op*`.
#[derive(Debug)]
pub(super) struct SBlock {
    pub label: String,
    pub params: Vec<SDef>,
    pub ops: Vec<SOp>,
}

/// `value ':' type`.
#[derive(Debug)]
pub(super) struct SDef {
    pub name: String,
    pub pos: TextPos,
    pub ty: SType,
}

/// `type ::= word | word '(' attrs? ')'`.
#[derive(Debug)]
pub(super) struct SType {
    pub ty: Type,
    pub pos: TextPos,
}

/// `op ::= (defs '=')? word attr* operands? region* locref`.
#[derive(Debug)]
pub(super) struct SOp {
    pub results: Vec<SDef>,
    pub name: String,
    pub name_pos: TextPos,
    pub attrs: Vec<Attr>,
    pub operands: Vec<(String, TextPos)>,
    pub succs: Vec<Succ>,
    pub regions: Vec<Vec<SBlock>>,
    pub loc: LocRef,
}

/// `module ::= item* locs`.
#[derive(Debug)]
pub(super) struct SModule {
    pub items: Vec<SItem>,
    pub locs: LocTable,
}
