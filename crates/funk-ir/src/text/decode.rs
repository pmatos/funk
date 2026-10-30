//! Decodes what the grammar leaves generic (`lean/Fir/Text/Grammar.lean`,
//! "Reading a text").
//!
//! Each item is decoded from its kind, each type through the registry, and
//! each op from its name, its attributes and the types of its operands and
//! results, found where those values are defined in the function. A text
//! that follows the grammar but does not decode is not a module: it is a
//! parse error with a position (ADR-2026-10-30-0815). Successor arguments are
//! not decoded: one that the function does not define is a validation error.

use std::collections::HashMap;

use super::syntax::{SBlock, SBody, SDef, SItem, SModule, SOp, SType};
use super::{ParseError, TextPos};
use crate::ir::{Block, Def, Func, Item, Module, Op, Region, Type};
use crate::registry::{OpTypes, Registry, TypeCheck};

fn err<T>(pos: TextPos, reason: impl Into<String>) -> Result<T, ParseError> {
    Err(ParseError {
        pos,
        reason: reason.into(),
    })
}

/// Decodes a module read by the grammar.
pub(super) fn module(s: SModule, reg: &Registry) -> Result<Module, ParseError> {
    let items = s
        .items
        .into_iter()
        .map(|i| item(i, reg))
        .collect::<Result<_, _>>()?;
    Ok(Module {
        items,
        locs: s.locs,
    })
}

/// In M0 every item is a `func`, with no attributes and with blocks in its
/// body. Every other item is of a kind the parser does not know.
fn item(s: SItem, reg: &Registry) -> Result<Item, ParseError> {
    if s.kind != "func" {
        return err(
            s.kind_pos,
            format!("unknown item kind {}: M0 has only func", s.kind),
        );
    }
    if let Some((_, pos)) = s.attrs.first() {
        return err(*pos, "a func has no attributes");
    }
    match s.body {
        SBody::Items(items) => err(items[0].kind_pos, "a func's body holds blocks, not items"),
        SBody::Blocks(blocks) => func(s.name, s.params, s.results, blocks, reg),
    }
}

fn func(
    name: String,
    params: Vec<SDef>,
    results: Vec<SType>,
    blocks: Vec<SBlock>,
    reg: &Registry,
) -> Result<Item, ParseError> {
    let mut scope = Scope {
        types: HashMap::new(),
        reg,
        func: &name,
    };
    for t in &results {
        scope.check_type(t)?;
    }
    for d in &params {
        scope.define(d)?;
    }
    for b in &blocks {
        scope.define_block(b)?;
    }
    let results = results.into_iter().map(|t| t.ty).collect();
    let params = params.into_iter().map(def).collect();
    let blocks = scope.blocks(blocks)?;
    Ok(Item::Func(Func {
        name,
        params,
        results,
        body: Region { blocks },
    }))
}

fn def(d: SDef) -> Def {
    Def {
        name: d.name,
        ty: d.ty.ty,
    }
}

/// The values a function defines, at any depth, with their types.
struct Scope<'a> {
    types: HashMap<String, Type>,
    reg: &'a Registry,
    func: &'a str,
}

impl Scope<'_> {
    fn check_type(&self, t: &SType) -> Result<(), ParseError> {
        match self.reg.check_type(&t.ty) {
            TypeCheck::Malformed(reason) => {
                err(t.pos, format!("type {} does not decode: {reason}", t.ty))
            }
            TypeCheck::Valid | TypeCheck::Invalid(_) => Ok(()),
        }
    }

    fn define(&mut self, d: &SDef) -> Result<(), ParseError> {
        self.check_type(&d.ty)?;
        if self.types.insert(d.name.clone(), d.ty.ty.clone()).is_some() {
            return err(d.pos, format!("value %{} is defined twice", d.name));
        }
        Ok(())
    }

    fn define_block(&mut self, b: &SBlock) -> Result<(), ParseError> {
        for d in &b.params {
            self.define(d)?;
        }
        for op in &b.ops {
            for d in &op.results {
                self.define(d)?;
            }
            for region in &op.regions {
                for inner in region {
                    self.define_block(inner)?;
                }
            }
        }
        Ok(())
    }

    fn blocks(&self, blocks: Vec<SBlock>) -> Result<Vec<Block>, ParseError> {
        blocks.into_iter().map(|b| self.block(b)).collect()
    }

    fn block(&self, b: SBlock) -> Result<Block, ParseError> {
        let ops = b
            .ops
            .into_iter()
            .map(|o| self.op(o))
            .collect::<Result<_, _>>()?;
        Ok(Block {
            label: b.label,
            params: b.params.into_iter().map(def).collect(),
            ops,
        })
    }

    fn op(&self, s: SOp) -> Result<Op, ParseError> {
        let Some(spec) = self.reg.op(&s.name) else {
            return err(s.name_pos, format!("unknown op {}", s.name));
        };
        let mut operand_types = Vec::with_capacity(s.operands.len());
        for (x, pos) in &s.operands {
            match self.types.get(x) {
                Some(t) => operand_types.push(t.clone()),
                None => return err(*pos, format!("value %{x} is not defined in @{}", self.func)),
            }
        }
        let results: Vec<Def> = s.results.into_iter().map(def).collect();
        let result_types: Vec<Type> = results.iter().map(|d| d.ty.clone()).collect();
        let types = OpTypes {
            attrs: &s.attrs,
            operands: &operand_types,
            results: &result_types,
        };
        if let Err(reason) = spec.decode(&types) {
            return err(
                s.name_pos,
                format!("op {} does not decode: {reason}", s.name),
            );
        }
        let regions = s
            .regions
            .into_iter()
            .map(|r| {
                Ok(Region {
                    blocks: self.blocks(r)?,
                })
            })
            .collect::<Result<_, ParseError>>()?;
        Ok(Op {
            results,
            name: s.name,
            attrs: s.attrs,
            operands: s.operands.into_iter().map(|(x, _)| x).collect(),
            succs: s.succs,
            regions,
            loc: s.loc,
        })
    }
}
