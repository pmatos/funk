//! A text read by the grammar of `lean/Fir/Text/Grammar.lean`, before
//! anything is decoded.
//!
//! Items keep the generic shape of the grammar, with no node for any kind
//! of item. A body of blocks is read straight into the IR's blocks and ops,
//! which are generic already, and the position of each part that decoding
//! can reject is kept beside them: a kind, an attribute, a type, a
//! definition, an op's name and each operand.

use super::TextPos;
use crate::ir::tree::drop_all;
use crate::ir::{Attr, Block, Def, LocTable, Type};

/// Where a definition `%x: T` stands: its name and its type.
#[derive(Clone, Copy, Debug)]
pub(super) struct DefPos {
    pub name: TextPos,
    pub ty: TextPos,
}

/// `item ::= word symbol '(' defs? ')' ('->' types)? attr* '{' body '}'`.
pub(super) struct SItem {
    pub kind: String,
    pub kind_pos: TextPos,
    pub name: String,
    pub params: Vec<(Def, DefPos)>,
    pub results: Vec<(Type, TextPos)>,
    pub attrs: Vec<(Attr, TextPos)>,
    pub body: SBody,
}

/// `body ::= block* | item*`. An empty body is an empty list of blocks.
pub(super) enum SBody {
    Blocks(Vec<Block>, BodyPos),
    Items(Vec<SItem>),
}

/// Where the parts of a body of blocks stand, each list in the order of the
/// text, which is the order of a depth-first walk of the blocks.
#[derive(Default)]
pub(super) struct BodyPos {
    /// Each argument of a block and each result of an op.
    pub defs: Vec<DefPos>,
    /// The name of each op.
    pub ops: Vec<TextPos>,
    /// Each operand of each op.
    pub operands: Vec<TextPos>,
}

impl Drop for SBody {
    /// Items nest to any depth, so they are dropped one at a time
    /// (ADR-2026-10-30-1333).
    fn drop(&mut self) {
        if let SBody::Items(items) = self {
            drop_all(std::mem::take(items), |item, rest| {
                if let SBody::Items(inner) = &mut item.body {
                    rest.append(inner);
                }
            });
        }
    }
}

/// `module ::= item* locs`.
pub(super) struct SModule {
    pub items: Vec<SItem>,
    pub locs: LocTable,
}
