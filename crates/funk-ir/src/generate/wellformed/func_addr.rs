//! Addresses of functions that the text writes and reads back, whether or
//! not validation accepts them (#235): `funcaddr` of a function of the
//! module or of a symbol that names none, with a pointer result of memory 0
//! or of any other memory, in blocks at any depth, of the module's functions
//! and of its nested modules'.

use super::super::{Rng, symbol};
use super::Shaper;
use crate::dialects::core::MAX_MEMORY;
use crate::ir::{Attr, Func, Op};

impl Shaper<'_> {
    /// Adds one or two `funcaddr` ops to blocks of `f` at any depth; `f`
    /// must have a block.
    pub(super) fn add_func_addrs(&mut self, rng: &mut Rng, f: &mut Func) {
        self.add_one_or_two(rng, f, Self::func_addr);
    }

    /// `funcaddr` of a function of the table three times in four when it has
    /// one, else of any symbol, with a pointer result of memory 0 three
    /// times in four and of any other memory otherwise.
    fn func_addr(&mut self, rng: &mut Rng) -> Op {
        let func = if !self.symbols.is_empty() && !rng.one_in(4) {
            rng.pick(self.symbols).clone()
        } else {
            symbol(rng)
        };
        let n = match rng.below(4) {
            0..=2 => 0,
            _ if rng.one_in(2) => 1 + rng.below(3) as u32,
            _ => MAX_MEMORY,
        };
        let mut op = Op::new("funcaddr", self.loc(rng)).attr(Attr::Sym(func));
        op.results.push(self.define_pointer(rng, n));
        op
    }
}
