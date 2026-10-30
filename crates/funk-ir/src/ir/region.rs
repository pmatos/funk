//! Regions nest to any depth (ADR-2026-10-30-1333): an op owns regions,
//! which hold blocks of ops, which own regions in turn.
//!
//! A [`Part`] is a region, a block or an op, and a walk over parts reaches
//! every block and op under a region, at any depth. `Region` is where the
//! nesting turns, so it writes by hand, from such walks, the traits that
//! `#[derive]` would write recursively: `Clone`, `PartialEq`, `Hash`,
//! `Debug` and `Drop`. `Block` and `Op` derive theirs, which call the
//! region's for their regions and so never recurse.

use std::fmt;
use std::hash::{Hash, Hasher};

use super::debug::{Bracket, DebugTree};
use super::module::{Block, Op, Region};
use super::tree::{self, Nest, Node, Step, walk};

/// A region, a block or an op: a node of a walk over regions.
#[derive(Clone, Copy)]
pub(crate) enum Part<'a> {
    Region(&'a Region),
    Block(&'a Block),
    Op(&'a Op),
}

/// The children of a part: a region's blocks, a block's ops or an op's
/// regions.
pub(crate) enum Parts<'a> {
    Blocks(std::slice::Iter<'a, Block>),
    Ops(std::slice::Iter<'a, Op>),
    Regions(std::slice::Iter<'a, Region>),
}

impl<'a> Iterator for Parts<'a> {
    type Item = Part<'a>;

    fn next(&mut self) -> Option<Part<'a>> {
        match self {
            Parts::Blocks(i) => i.next().map(Part::Block),
            Parts::Ops(i) => i.next().map(Part::Op),
            Parts::Regions(i) => i.next().map(Part::Region),
        }
    }
}

impl<'a> Node for Part<'a> {
    type Children = Parts<'a>;

    fn children(self) -> Parts<'a> {
        match self {
            Part::Region(r) => Parts::Blocks(r.blocks.iter()),
            Part::Block(b) => Parts::Ops(b.ops.iter()),
            Part::Op(o) => Parts::Regions(o.regions.iter()),
        }
    }

    fn is_leaf(self) -> bool {
        match self {
            Part::Region(r) => r.blocks.is_empty(),
            Part::Block(b) => b.ops.is_empty(),
            Part::Op(o) => o.regions.is_empty(),
        }
    }
}

impl Region {
    /// The blocks and ops under this region, at any depth, in depth-first
    /// order: each block, then each of its ops followed by the parts of the
    /// op's regions.
    pub(crate) fn parts(&self) -> impl Iterator<Item = Part<'_>> {
        walk(Part::Region(self)).skip(1).filter_map(Step::entered)
    }
}

/// A block with the label and arguments of `b`, and room for its ops.
fn block_head(b: &Block) -> Block {
    Block {
        label: b.label.clone(),
        params: b.params.clone(),
        ops: Vec::with_capacity(b.ops.len()),
    }
}

/// An op with every part of `o` but its regions, and room for them.
fn op_head(o: &Op) -> Op {
    Op {
        results: o.results.clone(),
        name: o.name.clone(),
        attrs: o.attrs.clone(),
        operands: o.operands.clone(),
        succs: o.succs.clone(),
        regions: Vec::with_capacity(o.regions.len()),
        loc: o.loc,
    }
}

impl Clone for Region {
    fn clone(&self) -> Region {
        let mut blocks = Nest::new(self.blocks.len());
        for step in walk(Part::Region(self)).skip(1) {
            match step {
                Step::Enter(Part::Region(r)) => blocks.open(r.blocks.len()),
                Step::Enter(Part::Block(b)) => blocks.push(block_head(b)),
                Step::Enter(Part::Op(o)) => {
                    let block = blocks.last_mut().expect("an op is in a block");
                    block.ops.push(op_head(o));
                }
                Step::Leave(Part::Region(_)) => {
                    if let Some((inner, owner)) = blocks.close() {
                        let op = owner.ops.last_mut().expect("the block holds the op");
                        op.regions.push(Region { blocks: inner });
                    }
                }
                Step::Leave(_) => {}
            }
        }
        Region {
            blocks: blocks.finish(),
        }
    }
}

/// Whether two parts are equal but for the parts under them.
fn same_head(a: Part<'_>, b: Part<'_>) -> bool {
    match (a, b) {
        (Part::Region(_), Part::Region(_)) => true,
        (Part::Block(x), Part::Block(y)) => x.label == y.label && x.params == y.params,
        (Part::Op(x), Part::Op(y)) => {
            x.results == y.results
                && x.name == y.name
                && x.attrs == y.attrs
                && x.operands == y.operands
                && x.succs == y.succs
                && x.loc == y.loc
        }
        _ => false,
    }
}

impl PartialEq for Region {
    fn eq(&self, other: &Region) -> bool {
        tree::equal(Part::Region(self), Part::Region(other), same_head)
    }
}

impl Eq for Region {}

impl Hash for Region {
    fn hash<H: Hasher>(&self, state: &mut H) {
        tree::hash(Part::Region(self), state, |p, state| match p {
            Part::Region(_) => state.write_u8(0),
            Part::Block(b) => {
                state.write_u8(1);
                (&b.label, &b.params).hash(state);
            }
            Part::Op(o) => {
                state.write_u8(2);
                (&o.results, &o.name, &o.attrs, &o.operands, &o.succs, o.loc).hash(state);
            }
        });
    }
}

impl fmt::Debug for Region {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = DebugTree::new(f);
        for step in walk(Part::Region(self)) {
            match step {
                Step::Enter(Part::Region(_)) => {
                    out.open(None, "Region", Bracket::Struct)?;
                    out.open(Some("blocks"), "", Bracket::List)?;
                }
                Step::Enter(Part::Block(b)) => {
                    out.open(None, "Block", Bracket::Struct)?;
                    out.value(Some("label"), &b.label)?;
                    out.value(Some("params"), &b.params)?;
                    out.open(Some("ops"), "", Bracket::List)?;
                }
                Step::Enter(Part::Op(o)) => {
                    out.open(None, "Op", Bracket::Struct)?;
                    out.value(Some("results"), &o.results)?;
                    out.value(Some("name"), &o.name)?;
                    out.value(Some("attrs"), &o.attrs)?;
                    out.value(Some("operands"), &o.operands)?;
                    out.value(Some("succs"), &o.succs)?;
                    out.open(Some("regions"), "", Bracket::List)?;
                }
                Step::Leave(Part::Op(o)) => {
                    out.close()?;
                    out.value(Some("loc"), &o.loc)?;
                    out.close()?;
                }
                Step::Leave(_) => {
                    out.close()?;
                    out.close()?;
                }
            }
        }
        Ok(())
    }
}

impl Drop for Region {
    fn drop(&mut self) {
        tree::drop_all(std::mem::take(&mut self.blocks), |b, rest| {
            for op in &mut b.ops {
                for r in &mut op.regions {
                    rest.append(&mut r.blocks);
                }
            }
        });
    }
}
