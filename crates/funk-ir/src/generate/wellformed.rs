//! A generator of random well-formed modules that are not all valid (#146).
//!
//! The round trip holds for every well-formed module (ADR-2026-10-30-0815,
//! `Module.WellFormed` in `lean/Fir/Text/RoundTrip.lean`), a larger set than
//! the valid modules that [`super::module`] makes. This generator starts from
//! one of those and adds what validation rejects but the text can still
//! write and read back:
//!
//! - ops that own regions, at any depth up to three, whose blocks hold ops,
//!   arguments and branches of their own;
//! - string attributes and applied attributes, `h()` and `h(1, "s", g(x))`
//!   among them, on the toy op [`TOY_OP`], which decodes with any
//!   attributes: no core op or type takes one;
//! - fused locations of no reference and of one;
//! - blocks that no branch reaches;
//! - successors whose block or argument the function does not define, and
//!   calls of symbols that name no function of the module;
//! - broken location tables (`locs.rs`), and ops whose location reference
//!   is in no entry.
//!
//! Each new op still decodes: its operands are values the function defines,
//! somewhere, of the types its name and attributes need, and its results
//! have new names. The parser finds an operand's type wherever its
//! definition stands, at any depth (`Func.typeOf`), so an op may use a value
//! defined later, in another block or in a region.
//!
//! With [`Dialects::Core`] a module holds only core ops, and regions go on
//! core ops, so `fir-ref`, which parses with the core dialect, reads it too:
//! the cross-language round trip uses those modules. [`Dialects::CoreAndToy`]
//! adds [`TOY_OP`], which a registry knows once it registers
//! [`toy_dialect`]. A module may name one to three dialects in its dialect
//! set, drawn with repeats, which the round trips print and read back
//! whatever dialects the reader holds. The generator is deterministic: one seed gives one module.

use super::{Rng, Widths, constant, name, string, symbol, width};
use crate::dialects::core::{self, int_type};
use crate::ir::{Attr, Block, Def, Func, Item, LocRef, Module, Op, Region, Succ, Type};
use crate::registry::{Dialect, OpShape, OpSpec, OpTypes};

mod locs;

/// How many modules, from seed 0, the round trips over well-formed modules
/// generate, of each kind of [`Dialects`].
pub const WELL_FORMED_MODULES: u64 = 600;

/// The toy op: any attributes, operands, results and regions decode.
pub const TOY_OP: &str = "toy.any";

/// The dialects whose ops a generated module holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dialects {
    /// The core dialect's ops only.
    Core,
    /// The core dialect's ops and [`TOY_OP`].
    CoreAndToy,
}

/// [`TOY_OP`]'s rule: every instance decodes, and validation checks
/// nothing of its own.
struct AnyOp;

impl OpSpec for AnyOp {
    fn name(&self) -> &str {
        TOY_OP
    }

    fn decode(&self, _op: &OpTypes<'_>) -> Result<OpShape, String> {
        Ok(OpShape::default())
    }
}

/// The test dialect `toy` with its one op, [`TOY_OP`], over the core. Test
/// dialects are named `toy`, so their ops are `toy.` and a word
/// (ADR-2026-11-09-1543).
pub fn toy_dialect() -> Dialect {
    Dialect::new("toy").depends_on(core::NAME).op(AnyOp)
}

/// A random well-formed module, which validation often rejects.
pub fn module(rng: &mut Rng, dialects: Dialects) -> Module {
    let mut m = super::module(rng);
    if m.items.is_empty() && !rng.one_in(4) {
        let entry = Block::new(name(rng, false));
        m = m.func(Func::new(symbol(rng)).block(entry));
    }
    let symbols: Vec<String> = m.funcs().map(|f| f.name.clone()).collect();
    let keys: Vec<LocRef> = m.locs.entries.iter().map(|(r, _)| *r).collect();
    for item in &mut m.items {
        let Item::Func(f) = item;
        let mut shaper = Shaper::new(f, &symbols, &keys, dialects == Dialects::CoreAndToy);
        shaper.reshape(rng, f);
    }
    if rng.one_in(2) {
        locs::add_short_fused(rng, &mut m.locs);
    }
    if rng.one_in(2) {
        locs::break_table(rng, &mut m.locs);
    }
    if rng.one_in(4) {
        for _ in 0..=rng.below(3) {
            m.dialects
                .push(rng.pick(&["toy", "gpu", "x_1"]).to_string());
        }
    }
    m
}

/// What a function defines, and what its new ops may name.
struct Shaper<'m> {
    /// The symbols of the module's functions.
    symbols: &'m [String],
    /// The references of the module's location table.
    keys: &'m [LocRef],
    /// Whether [`TOY_OP`] may be used.
    toy: bool,
    /// Every value the function defines, at any depth, with its type.
    values: Vec<(String, Type)>,
    /// Every value name taken: defined, or named as undefined.
    taken: Vec<String>,
    /// Every label taken: of a block at any depth, or named as undefined.
    labels: Vec<String>,
}

impl<'m> Shaper<'m> {
    fn new(f: &Func, symbols: &'m [String], keys: &'m [LocRef], toy: bool) -> Shaper<'m> {
        let mut values: Vec<(String, Type)> = Vec::new();
        values.extend(f.params.iter().map(|d| (d.name.clone(), d.ty.clone())));
        for b in &f.body.blocks {
            values.extend(b.params.iter().map(|d| (d.name.clone(), d.ty.clone())));
            for op in &b.ops {
                values.extend(op.results.iter().map(|d| (d.name.clone(), d.ty.clone())));
            }
        }
        Shaper {
            symbols,
            keys,
            toy,
            taken: values.iter().map(|(v, _)| v.clone()).collect(),
            values,
            labels: f.body.blocks.iter().map(|b| b.label.clone()).collect(),
        }
    }

    /// Adds to `f`, each one often: regions, blocks that no branch reaches,
    /// successors that are not defined, calls of symbols that are not, and
    /// toy ops with string and applied attributes.
    fn reshape(&mut self, rng: &mut Rng, f: &mut Func) {
        if f.body.blocks.is_empty() {
            return;
        }
        if rng.one_in(2) {
            for _ in 0..1 + rng.below(3) {
                let b = rng.below(f.body.blocks.len() as u64) as usize;
                let ops = &mut f.body.blocks[b].ops;
                if ops.is_empty() || (self.toy && rng.one_in(2)) {
                    let mut op = self.toy_op(rng);
                    self.add_regions(rng, &mut op, 1);
                    insert(rng, ops, op);
                } else {
                    let k = rng.below(ops.len() as u64) as usize;
                    self.add_regions(rng, &mut ops[k], 1);
                }
            }
        }
        if rng.one_in(2) {
            for _ in 0..1 + rng.below(2) {
                let block = self.block(rng, 1);
                f.body.blocks.push(block);
            }
        }
        if rng.one_in(2) {
            self.undefined_successor(rng, f);
        }
        if rng.one_in(2) {
            let op = self.call(rng, true);
            let b = rng.below(f.body.blocks.len() as u64) as usize;
            insert(rng, &mut f.body.blocks[b].ops, op);
        }
        if self.toy && rng.one_in(2) {
            for _ in 0..1 + rng.below(3) {
                let op = self.toy_op(rng);
                let b = rng.below(f.body.blocks.len() as u64) as usize;
                insert(rng, &mut f.body.blocks[b].ops, op);
            }
        }
    }

    /// Makes a successor of a terminator of `f` name a block or a value
    /// that `f` does not define, or adds a `br` to a block it does not.
    fn undefined_successor(&mut self, rng: &mut Rng, f: &mut Func) {
        let label = self.undefined_label(rng);
        let arg = self.undefined_value(rng);
        let b = rng.below(f.body.blocks.len() as u64) as usize;
        let ops = &mut f.body.blocks[b].ops;
        match ops.iter_mut().rev().find(|op| !op.succs.is_empty()) {
            Some(op) => {
                let k = rng.below(op.succs.len() as u64) as usize;
                if rng.one_in(2) {
                    op.succs[k].label = label;
                } else {
                    let at = rng.below(op.succs[k].args.len() as u64 + 1) as usize;
                    op.succs[k].args.insert(at, arg);
                }
            }
            None => {
                let mut br = Op::new("br", self.loc(rng));
                br.succs.push(Succ::new(label, vec![arg]));
                ops.push(br);
            }
        }
    }

    /// A reference for an op: one of the table's, or now and then one
    /// that is in no entry.
    fn loc(&self, rng: &mut Rng) -> LocRef {
        if self.keys.is_empty() || rng.one_in(10) {
            LocRef(rng.next_u64() as u32)
        } else {
            *rng.pick(self.keys)
        }
    }

    fn fresh(rng: &mut Rng, taken: &mut Vec<String>) -> String {
        let mut n = name(rng, false);
        while taken.contains(&n) {
            n = format!("{n}.{}", taken.len());
        }
        taken.push(n.clone());
        n
    }

    /// A new value of type `t`, which the caller defines.
    fn define(&mut self, rng: &mut Rng, t: Type) -> Def {
        let n = Self::fresh(rng, &mut self.taken);
        self.values.push((n.clone(), t.clone()));
        Def::new(n, t)
    }

    fn undefined_value(&mut self, rng: &mut Rng) -> String {
        Self::fresh(rng, &mut self.taken)
    }

    fn undefined_label(&mut self, rng: &mut Rng) -> String {
        Self::fresh(rng, &mut self.labels)
    }

    /// A type: often one that a value of the function has.
    fn ty(&self, rng: &mut Rng) -> Type {
        if !self.values.is_empty() && rng.one_in(2) {
            rng.pick(&self.values).1.clone()
        } else {
            int_type(width(rng, Widths::Any))
        }
    }

    /// A block of up to two arguments and up to three ops, with a new label.
    fn block(&mut self, rng: &mut Rng, depth: u32) -> Block {
        let mut b = Block::new(Self::fresh(rng, &mut self.labels));
        for _ in 0..rng.below(3) {
            let t = self.ty(rng);
            b.params.push(self.define(rng, t));
        }
        for _ in 0..rng.below(4) {
            let op = self.op(rng, depth);
            b.ops.push(op);
        }
        b
    }

    /// Gives `op` one or two regions of up to three blocks each.
    fn add_regions(&mut self, rng: &mut Rng, op: &mut Op, depth: u32) {
        for _ in 0..1 + rng.below(2) {
            let blocks = (0..rng.below(4)).map(|_| self.block(rng, depth)).collect();
            op.regions.push(Region::new(blocks));
        }
    }

    /// A random op of the function: a constant, an op on values it
    /// defines, a call, a branch, a return or a toy op; below depth three,
    /// it may own regions.
    fn op(&mut self, rng: &mut Rng, depth: u32) -> Op {
        let mut op = match rng.below(7) {
            0 => {
                let undefined = rng.one_in(2);
                self.call(rng, undefined)
            }
            1 => {
                let mut op = Op::new("ret", self.loc(rng));
                op.operands = self.uses(rng);
                op
            }
            2 => self.branch(rng),
            3 if self.toy => self.toy_op(rng),
            4 | 5 if !self.values.is_empty() => {
                let (x, t) = rng.pick(&self.values).clone();
                let y = self.use_of(rng, &t).unwrap_or_else(|| x.clone());
                let (name, operands) = match rng.below(3) {
                    0 => ("freeze", vec![x]),
                    1 => ("add", vec![x, y]),
                    _ => ("xor", vec![y, x]),
                };
                let mut op = Op::new(name, self.loc(rng));
                op.operands = operands;
                op.results.push(self.define(rng, t));
                op
            }
            _ => {
                let w = width(rng, Widths::Any);
                let op = Op::new("const", self.loc(rng)).attr(constant(rng, w));
                let d = self.define(rng, int_type(w));
                Op {
                    results: vec![d],
                    ..op
                }
            }
        };
        if depth < 3 && rng.one_in(4) {
            self.add_regions(rng, &mut op, depth + 1);
        }
        op
    }

    /// Up to two values the function defines, of any types.
    fn uses(&self, rng: &mut Rng) -> Vec<String> {
        if self.values.is_empty() {
            return Vec::new();
        }
        let n = rng.below(3);
        (0..n).map(|_| rng.pick(&self.values).0.clone()).collect()
    }

    /// A value of type `t` that the function defines, if there is one.
    fn use_of(&self, rng: &mut Rng, t: &Type) -> Option<String> {
        let same: Vec<&String> = self
            .values
            .iter()
            .filter(|(_, u)| u == t)
            .map(|(v, _)| v)
            .collect();
        (!same.is_empty()).then(|| rng.pick(&same).to_string())
    }

    /// A `br` to one block, or a `cond_br` on an `i1` to two: blocks of the
    /// function or not, passing values it defines or not.
    fn branch(&mut self, rng: &mut Rng) -> Op {
        let i1 = int_type(1);
        let mut op = Op::new("br", self.loc(rng));
        if let Some(c) = self.use_of(rng, &i1).filter(|_| rng.one_in(2)) {
            op = Op::new("cond_br", op.loc).operand(c);
        }
        let count = if op.name == "br" { 1 } else { 2 };
        for _ in 0..count {
            let label = if rng.one_in(3) {
                self.undefined_label(rng)
            } else {
                rng.pick(&self.labels).clone()
            };
            let args = (0..rng.below(3))
                .map(|_| {
                    if self.values.is_empty() || rng.one_in(4) {
                        self.undefined_value(rng)
                    } else {
                        rng.pick(&self.values).0.clone()
                    }
                })
                .collect();
            op.succs.push(Succ::new(label, args));
        }
        op
    }

    /// A `call`, of a symbol that names no function of the module when
    /// `undefined` is set or the module has none, with values the function
    /// defines and results of any types.
    fn call(&mut self, rng: &mut Rng, undefined: bool) -> Op {
        let callee = if undefined || self.symbols.is_empty() {
            loop {
                let s = symbol(rng);
                if !self.symbols.contains(&s) {
                    break s;
                }
            }
        } else {
            rng.pick(self.symbols).clone()
        };
        let mut op = Op::new("call", self.loc(rng)).attr(Attr::Sym(callee));
        op.operands = self.uses(rng);
        for _ in 0..rng.below(3) {
            let t = self.ty(rng);
            op.results.push(self.define(rng, t));
        }
        op
    }

    /// [`TOY_OP`] with up to three attributes, and up to two operands and
    /// results; the core op `const` when the toy op may not be used.
    fn toy_op(&mut self, rng: &mut Rng) -> Op {
        if !self.toy {
            let op = Op::new("const", self.loc(rng)).attr(Attr::word("true"));
            let d = self.define(rng, int_type(1));
            return Op {
                results: vec![d],
                ..op
            };
        }
        let mut op = Op::new(TOY_OP, self.loc(rng));
        op.attrs = (0..rng.below(4)).map(|_| attr(rng, 0)).collect();
        op.operands = self.uses(rng);
        for _ in 0..rng.below(3) {
            let t = self.ty(rng);
            op.results.push(self.define(rng, t));
        }
        op
    }
}

/// Inserts `op` anywhere in `ops`: before, among or after the others.
fn insert(rng: &mut Rng, ops: &mut Vec<Op>, op: Op) {
    let at = rng.below(ops.len() as u64 + 1) as usize;
    ops.insert(at, op);
}

/// An attribute of any kind, often a string or an applied word, which
/// nests below depth three.
fn attr(rng: &mut Rng, depth: u32) -> Attr {
    match rng.below(if depth < 3 { 7 } else { 5 }) {
        0 | 1 => Attr::Str(string(rng)),
        2 => Attr::Word(name(rng, true)),
        3 => {
            let w = width(rng, Widths::Any);
            constant(rng, w)
        }
        4 => Attr::Sym(symbol(rng)),
        5 => Attr::App(name(rng, true), Vec::new()),
        _ => {
            let args = (0..1 + rng.below(3))
                .map(|_| attr(rng, depth + 1))
                .collect();
            Attr::App(name(rng, true), args)
        }
    }
}
