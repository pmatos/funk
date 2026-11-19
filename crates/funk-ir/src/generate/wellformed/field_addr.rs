//! Field addresses that the text writes and reads back, whether or not
//! validation accepts them (#236): `fieldaddr` of a layout of the module or
//! of a symbol that names none, a field of any number, a pointer of any
//! memory, and an index of any width or none.
//!
//! Each pointer comes from an `alloca` of its memory, or from an earlier
//! `fieldaddr`, so its type is known wherever the op stands. Pointers are
//! kept apart from the function's other values, which the generator also
//! passes to integer ops.

use super::super::{Rng, Widths, constant, symbol, width};
use super::{Shaper, insert};
use crate::dialects::core::{MAX_MEMORY, int_type, int_width, ptr_type};
use crate::ir::{Attr, Def, Func, Op};

impl Shaper<'_> {
    /// Adds one to three `fieldaddr` ops to blocks of `f`, which must have
    /// one, with the `alloca` that defines each new pointer.
    pub(super) fn add_field_addrs(&mut self, rng: &mut Rng, f: &mut Func, layouts: &[String]) {
        for _ in 0..1 + rng.below(3) {
            let mut ops = Vec::new();
            let pointer = self.pointer(rng, &mut ops);
            let op = self.field_addr(rng, pointer, layouts, &mut ops);
            ops.push(op);
            for op in ops {
                let b = rng.below(f.body.blocks.len() as u64) as usize;
                insert(rng, &mut f.body.blocks[b].ops, op);
            }
        }
    }

    /// A pointer the function defines, and its memory: an earlier one, or
    /// a new one that an `alloca` pushed on `ops` defines.
    fn pointer(&mut self, rng: &mut Rng, ops: &mut Vec<Op>) -> (String, u32) {
        if !self.pointers.is_empty() && rng.one_in(2) {
            return rng.pick(&self.pointers).clone();
        }
        let n = match rng.below(4) {
            0 | 1 => 0,
            2 => 1 + rng.below(3) as u32,
            _ => MAX_MEMORY,
        };
        let mut op = Op::new("alloca", self.loc(rng))
            .attr(Attr::word("stack"))
            .attr(Attr::word("i8"));
        op.results.push(self.define_pointer(rng, n));
        ops.push(op);
        (op_result(ops), n)
    }

    /// `fieldaddr` of `pointer`: of a layout from `layouts` three times in
    /// four when there is one, else of any symbol, often a function's; of a
    /// field of any number; and with an index in one draw of two. A new
    /// index is a `const` pushed on `ops`.
    fn field_addr(
        &mut self,
        rng: &mut Rng,
        (p, n): (String, u32),
        layouts: &[String],
        ops: &mut Vec<Op>,
    ) -> Op {
        let layout = if !layouts.is_empty() && !rng.one_in(4) {
            rng.pick(layouts).clone()
        } else if !self.symbols.is_empty() && rng.one_in(2) {
            rng.pick(self.symbols).clone()
        } else {
            symbol(rng)
        };
        let field = match rng.below(6) {
            0 => i128::from(u64::MAX),
            1 => 1 << 64,
            _ => i128::from(rng.below(4)),
        };
        let mut op = Op::new("fieldaddr", self.loc(rng))
            .attr(Attr::Sym(layout))
            .attr(Attr::int(field))
            .operand(p);
        if rng.one_in(2) {
            op = op.operand(self.index(rng, ops));
        }
        op.results.push(self.define_pointer(rng, n));
        op
    }

    /// An integer the function defines, or a new `const` pushed on `ops`.
    fn index(&mut self, rng: &mut Rng, ops: &mut Vec<Op>) -> String {
        let ints: Vec<&String> = self
            .values
            .iter()
            .filter(|(_, t)| int_width(t).is_some())
            .map(|(v, _)| v)
            .collect();
        if !ints.is_empty() && !rng.one_in(3) {
            return rng.pick(&ints).to_string();
        }
        let w = width(rng, Widths::Any);
        let op = Op::new("const", self.loc(rng)).attr(constant(rng, w));
        let d = self.define(rng, int_type(w));
        let name = d.name.clone();
        ops.push(Op {
            results: vec![d],
            ..op
        });
        name
    }

    /// A new pointer of memory `n`, which the caller defines.
    fn define_pointer(&mut self, rng: &mut Rng, n: u32) -> Def {
        let name = Self::fresh(rng, &mut self.taken);
        self.pointers.push((name.clone(), n));
        Def::new(name, ptr_type(n))
    }
}

/// The name of the one result of the last op of `ops`.
fn op_result(ops: &[Op]) -> String {
    ops.last().expect("an op").results[0].name.clone()
}
