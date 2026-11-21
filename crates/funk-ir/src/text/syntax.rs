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

/// `item ::= word symbol '(' params? ')' ('->' results)? attr* '{' body '}'`,
/// where each parameter and each result carries the attributes after its
/// type, and the parameters may end in `...`.
pub(super) struct SItem {
    pub kind: String,
    pub kind_pos: TextPos,
    pub name: String,
    pub params: Vec<(Def, DefPos)>,
    /// The attributes of each parameter.
    pub param_attrs: Vec<Vec<(Attr, TextPos)>>,
    /// Where the `...` that ends the parameters stands, if they end in it.
    pub variadic: Option<TextPos>,
    pub results: Vec<(Type, TextPos)>,
    /// The attributes of each result but the last, whose attributes start
    /// `attrs`.
    pub result_attrs: Vec<Vec<(Attr, TextPos)>>,
    pub attrs: Vec<(Attr, TextPos)>,
    pub body: SBody,
}

/// `body ::= block* | dialects? item*`. An empty body is an empty list of
/// blocks.
pub(super) enum SBody {
    Blocks(Vec<Block>, BodyPos),
    Items(Vec<String>, Vec<SItem>),
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
    /// (`docs/decisions/rust-ir-and-tools.md#nesting`).
    fn drop(&mut self) {
        if let SBody::Items(_, items) = self {
            drop_all(std::mem::take(items), |item, rest| {
                if let SBody::Items(_, inner) = &mut item.body {
                    rest.append(inner);
                }
            });
        }
    }
}

/// `module ::= dialects? layout? item* locs`.
pub(super) struct SModule {
    pub dialects: Vec<String>,
    /// Each entry of the data layout as written, with its position.
    pub layout: Vec<(Type, TextPos)>,
    pub items: Vec<SItem>,
    pub locs: LocTable,
}
