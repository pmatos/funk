//! Addresses of globals that the text writes and reads back, whether or not
//! validation accepts them (#237): `globaladdr` of a global of the module
//! or of a symbol that names none, with a pointer result of any memory, in
//! blocks at any depth, of the module's functions and of its nested
//! modules'.

use super::super::{Rng, symbol};
use super::Shaper;
use super::field_addr::any_block;
use super::insert;
use crate::dialects::core::MAX_MEMORY;
use crate::ir::{Attr, Func, Op};

impl Shaper<'_> {
    /// Adds one or two `globaladdr` ops to blocks of `f` at any depth; `f`
    /// must have a block.
    pub(super) fn add_global_addrs(&mut self, rng: &mut Rng, f: &mut Func, globals: &[String]) {
        for _ in 0..1 + rng.below(2) {
            let op = self.global_addr(rng, globals);
            let block = any_block(rng, &mut f.body.blocks);
            insert(rng, &mut block.ops, op);
        }
    }

    /// `globaladdr` of a global from `globals` three times in four when
    /// there is one, else of any symbol, often a function's, with a pointer
    /// result of memory 0 in one draw of two and of any other memory
    /// otherwise.
    fn global_addr(&mut self, rng: &mut Rng, globals: &[String]) -> Op {
        let global = if !globals.is_empty() && !rng.one_in(4) {
            rng.pick(globals).clone()
        } else if !self.symbols.is_empty() && rng.one_in(2) {
            rng.pick(self.symbols).clone()
        } else {
            symbol(rng)
        };
        let n = match rng.below(4) {
            0 | 1 => 0,
            2 => 1 + rng.below(3) as u32,
            _ => MAX_MEMORY,
        };
        let mut op = Op::new("globaladdr", self.loc(rng)).attr(Attr::Sym(global));
        op.results.push(self.define_pointer(rng, n));
        op
    }
}
