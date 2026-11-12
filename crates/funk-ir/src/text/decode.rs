//! Decodes what the grammar leaves generic (`lean/Fir/Text/Grammar.lean`,
//! "Reading a text").
//!
//! Each item is decoded from its kind, each type through the registry, and
//! each op from its name, its attributes and the types of its operands and
//! results, found where those values are defined in the function. A text
//! that follows the grammar but does not decode is not a module: it is a
//! parse error with a position (ADR-2026-10-29-2014). Successor arguments are
//! not decoded: one that the function does not define is a validation error.
//!
//! The blocks and ops of a body are walked in depth-first order, which is
//! the order of the text and of their positions, so that regions nest to any
//! depth (`docs/decisions/rust-ir-and-tools.md#nesting`).

use std::collections::HashMap;

use super::syntax::{BodyPos, DefPos, SBody, SItem, SModule};
use super::{ParseError, TextPos};
use crate::ir::names::is_dialect_word;
use crate::ir::tree::Nest;
use crate::ir::{Def, DialectItem, Func, Item, Module, NestedModule, Op, Part, Region, Type};
use crate::registry::{OpTypes, Registry, TypeCheck};

fn err<T>(pos: TextPos, reason: impl Into<String>) -> Result<T, ParseError> {
    Err(ParseError {
        pos,
        reason: reason.into(),
    })
}

/// Decodes a module read by the grammar.
pub(super) fn module(s: SModule, reg: &Registry) -> Result<Module, ParseError> {
    Ok(Module {
        dialects: s.dialects,
        items: items(s.items, reg)?,
        locs: s.locs,
    })
}

/// Decodes items in order, each at any depth. Modules nest to any depth
/// (`docs/decisions/rust-ir-and-tools.md#nesting`), so the lists of items that
/// enclose the one being decoded wait on a stack, and a nested module's items
/// are built in a [`Nest`]: each item is decoded whole before the next, depth
/// first, as the spec's decoder does.
fn items(s: Vec<SItem>, reg: &Registry) -> Result<Vec<Item>, ParseError> {
    let mut built = Nest::new(s.len());
    let mut todo = vec![s.into_iter()];
    while let Some(rest) = todo.last_mut() {
        match rest.next() {
            Some(i) => match item(i, reg)? {
                Decoded::Item(i) => built.push(i),
                Decoded::Module(m, body) => {
                    built.push(Item::Module(m));
                    built.open(body.len());
                    todo.push(body.into_iter());
                }
            },
            None => {
                todo.pop();
                built.close_module();
            }
        }
    }
    Ok(built.finish())
}

/// An item decoded but for the items of a nested module, which the caller
/// decodes.
enum Decoded {
    Item(Item),
    Module(NestedModule, Vec<SItem>),
}

/// A `func` has no attributes and blocks in its body. A `module` has no
/// parameters, results or attributes, and its dialect set and items in its
/// body (ADR-2026-11-10-1510). An empty body is no blocks, so it is a
/// function with no blocks or a module with no items. An item whose kind is
/// a word of a dialect has an empty body (ADR-2026-11-09-1543), whichever
/// dialect registers its kind, as validation asks. Every other item is of a
/// kind the parser does not know.
fn item(mut s: SItem, reg: &Registry) -> Result<Decoded, ParseError> {
    match s.kind.as_str() {
        "func" => func_item(s, reg).map(Decoded::Item),
        "module" => {
            if let Some((_, at)) = s.params.first() {
                return err(at.name, "a module has no parameters");
            }
            if let Some((_, pos)) = s.results.first() {
                return err(*pos, "a module has no results");
            }
            if let Some((_, pos)) = s.attrs.first() {
                return err(*pos, "a module has no attributes");
            }
            let (dialects, body) = match &mut s.body {
                SBody::Blocks(blocks, _) if blocks.is_empty() => (Vec::new(), Vec::new()),
                SBody::Blocks(..) => {
                    return err(s.kind_pos, "a module's body holds items, not blocks");
                }
                SBody::Items(dialects, body) => (std::mem::take(dialects), std::mem::take(body)),
            };
            let m = NestedModule {
                name: s.name,
                dialects,
                items: Vec::new(),
            };
            Ok(Decoded::Module(m, body))
        }
        kind if is_dialect_word(kind) => dialect_item(s, reg).map(Decoded::Item),
        _ => err(
            s.kind_pos,
            format!(
                "unknown item kind {}: the kinds are func, module and the words of dialects",
                s.kind
            ),
        ),
    }
}

/// An item of a dialect's kind (`decodeDialectItem`): its body is empty,
/// and its result types, then its parameters' types, decode. Its attributes
/// stay as the text writes them.
fn dialect_item(mut s: SItem, reg: &Registry) -> Result<Item, ParseError> {
    if !matches!(&s.body, SBody::Blocks(blocks, _) if blocks.is_empty()) {
        return err(s.kind_pos, "an item of a dialect's kind has an empty body");
    }
    for (t, pos) in &s.results {
        decode_type(reg, t, *pos)?;
    }
    for (d, at) in &s.params {
        decode_type(reg, &d.ty, at.ty)?;
    }
    Ok(Item::Dialect(DialectItem {
        kind: std::mem::take(&mut s.kind),
        name: std::mem::take(&mut s.name),
        params: std::mem::take(&mut s.params)
            .into_iter()
            .map(|(d, _)| d)
            .collect(),
        results: std::mem::take(&mut s.results)
            .into_iter()
            .map(|(t, _)| t)
            .collect(),
        attrs: std::mem::take(&mut s.attrs)
            .into_iter()
            .map(|(a, _)| a)
            .collect(),
    }))
}

/// An item of kind `func`.
fn func_item(mut s: SItem, reg: &Registry) -> Result<Item, ParseError> {
    if let Some((_, pos)) = s.attrs.first() {
        return err(*pos, "a func has no attributes");
    }
    let (blocks, at) = match &mut s.body {
        SBody::Items(dialects, _) if !dialects.is_empty() => {
            return err(s.kind_pos, "a func's body holds blocks, not a dialect set");
        }
        SBody::Items(_, items) => match items.first() {
            Some(first) => return err(first.kind_pos, "a func's body holds blocks, not items"),
            None => (Vec::new(), BodyPos::default()),
        },
        SBody::Blocks(blocks, at) => (std::mem::take(blocks), std::mem::take(at)),
    };
    let f = Func {
        name: s.name,
        params: Vec::new(),
        results: Vec::new(),
        body: Region::new(blocks),
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

/// Decodes the type `t`, which stands at `pos` (`decodeType`): a type that
/// the registry calls malformed does not decode.
fn decode_type(reg: &Registry, t: &Type, pos: TextPos) -> Result<(), ParseError> {
    match reg.check_type(t) {
        TypeCheck::Malformed(reason) => err(pos, format!("type {t} does not decode: {reason}")),
        TypeCheck::Valid | TypeCheck::Invalid(_) => Ok(()),
    }
}

impl Scope<'_> {
    fn check_type(&self, t: &Type, pos: TextPos) -> Result<(), ParseError> {
        decode_type(self.reg, t, pos)
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
