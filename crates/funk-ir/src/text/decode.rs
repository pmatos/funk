//! Decodes what the grammar leaves generic (`lean/Fir/Text/Grammar.lean`,
//! "Reading a text").
//!
//! Each item is decoded from its kind, each type through the registry, and
//! each op from its name, its attributes and the types of its operands and
//! results, found where those values are defined in the function. A text
//! that follows the grammar but does not decode is not a module: it is a
//! parse error with a position (ADR-2026-10-30-0815). Successor arguments are
//! not decoded: one that the function does not define is a validation error.
//!
//! The blocks and ops of a body are walked in depth-first order, which is
//! the order of the text and of their positions, so that regions nest to any
//! depth (ADR-2026-10-30-1333).

use std::collections::HashMap;

use super::syntax::{BodyPos, DefPos, SBody, SItem, SModule};
use super::{ParseError, TextPos};
use crate::ir::{Def, Func, Item, Module, Op, Part, Region, Type};
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
fn item(mut s: SItem, reg: &Registry) -> Result<Item, ParseError> {
    if s.kind != "func" {
        return err(
            s.kind_pos,
            format!("unknown item kind {}: M0 has only func", s.kind),
        );
    }
    if let Some((_, pos)) = s.attrs.first() {
        return err(*pos, "a func has no attributes");
    }
    let (blocks, at) = match &mut s.body {
        SBody::Items(items) => {
            return err(items[0].kind_pos, "a func's body holds blocks, not items");
        }
        SBody::Blocks(blocks, at) => (std::mem::take(blocks), std::mem::take(at)),
    };
    let f = Func {
        name: s.name,
        params: Vec::new(),
        results: Vec::new(),
        body: Region { blocks },
    };
    func(f, s.params, s.results, &at, reg)
}

/// Decodes a function whose body the grammar read: `f` with these
/// parameters and results.
fn func(
    mut f: Func,
    params: Vec<(Def, DefPos)>,
    results: Vec<(Type, TextPos)>,
    at: &BodyPos,
    reg: &Registry,
) -> Result<Item, ParseError> {
    let mut scope = Scope {
        types: HashMap::new(),
        reg,
        func: &f.name,
    };
    for (t, pos) in &results {
        scope.check_type(t, *pos)?;
    }
    for (d, pos) in &params {
        scope.define(d, *pos)?;
    }
    let mut def_pos = at.defs.iter().copied();
    for part in f.body.parts() {
        let defs = match part {
            Part::Block(b) => &b.params,
            Part::Op(op) => &op.results,
            Part::Region(_) => continue,
        };
        for d in defs {
            scope.define(d, def_pos.next().expect("a position per definition"))?;
        }
    }
    let mut name_pos = at.ops.iter().copied();
    let mut operand_pos = at.operands.iter().copied();
    for part in f.body.parts() {
        if let Part::Op(op) = part {
            let name = name_pos.next().expect("a position per op");
            scope.op(op, name, &mut operand_pos)?;
        }
    }
    f.params = params.into_iter().map(|(d, _)| d).collect();
    f.results = results.into_iter().map(|(t, _)| t).collect();
    Ok(Item::Func(f))
}

/// The values a function defines, at any depth, with their types.
struct Scope<'a> {
    types: HashMap<String, Type>,
    reg: &'a Registry,
    func: &'a str,
}

impl Scope<'_> {
    fn check_type(&self, t: &Type, pos: TextPos) -> Result<(), ParseError> {
        match self.reg.check_type(t) {
            TypeCheck::Malformed(reason) => err(pos, format!("type {t} does not decode: {reason}")),
            TypeCheck::Valid | TypeCheck::Invalid(_) => Ok(()),
        }
    }

    fn define(&mut self, d: &Def, at: DefPos) -> Result<(), ParseError> {
        self.check_type(&d.ty, at.ty)?;
        if self.types.insert(d.name.clone(), d.ty.clone()).is_some() {
            return err(at.name, format!("value %{} is defined twice", d.name));
        }
        Ok(())
    }

    /// Decodes `op`, whose name stands at `name_pos`; its operands stand at
    /// the next positions of `operand_pos`.
    fn op(
        &self,
        op: &Op,
        name_pos: TextPos,
        operand_pos: &mut impl Iterator<Item = TextPos>,
    ) -> Result<(), ParseError> {
        let Some(spec) = self.reg.op(&op.name) else {
            return err(name_pos, format!("unknown op {}", op.name));
        };
        let mut operand_types = Vec::with_capacity(op.operands.len());
        for x in &op.operands {
            let pos = operand_pos.next().expect("a position per operand");
            match self.types.get(x) {
                Some(t) => operand_types.push(t.clone()),
                None => {
                    let func = super::print_symbol(self.func);
                    return err(pos, format!("value %{x} is not defined in {func}"));
                }
            }
        }
        let result_types: Vec<Type> = op.results.iter().map(|d| d.ty.clone()).collect();
        let types = OpTypes {
            attrs: &op.attrs,
            operands: &operand_types,
            results: &result_types,
        };
        if let Err(reason) = spec.decode(&types) {
            return err(
                name_pos,
                format!("op {} does not decode: {reason}", op.name),
            );
        }
        Ok(())
    }
}
