//! The builder: chained constructors for every part of the IR.
//!
//! [`Op::new`] takes the op's location, so no op can be built without one
//! (H8, ADR-2026-10-29-2013); `unknown` is a location like any other. The
//! builder checks nothing else: an op it builds may be ill-typed, and the
//! verifier says so.
//!
//! ```
//! use funk_ir::{Block, Func, Location, Module, Op, dialects::core};
//!
//! let mut m = Module::new();
//! let here = m.locs.push(Location::Unknown);
//! let i32 = core::int_type(32);
//! let f = Func::new("seven")
//!     .result(i32.clone())
//!     .block(
//!         Block::new("entry")
//!             .op(Op::new("const", here).attr(funk_ir::Attr::int(7)).result("c", i32))
//!             .op(Op::new("ret", here).operand("c")),
//!     );
//! m = m.func(f);
//! assert!(funk_ir::verify(&m, &funk_ir::Registry::core()).is_empty());
//! ```
//!
//! An op without a location does not compile:
//!
//! ```compile_fail
//! let op = funk_ir::Op::new("ret");
//! ```

use super::attr::{Attr, Type};
use super::location::LocRef;
use super::module::{Block, Def, Func, Item, Module, Op, Region, Succ};

impl Op {
    /// An op named `name` at location `loc`, with no parts yet.
    pub fn new(name: impl Into<String>, loc: LocRef) -> Op {
        Op {
            results: Vec::new(),
            name: name.into(),
            attrs: Vec::new(),
            operands: Vec::new(),
            succs: Vec::new(),
            regions: Vec::new(),
            loc,
        }
    }

    /// Adds the result `%name: ty`.
    pub fn result(mut self, name: impl Into<String>, ty: Type) -> Op {
        self.results.push(Def::new(name, ty));
        self
    }

    /// Adds an attribute.
    pub fn attr(mut self, a: Attr) -> Op {
        self.attrs.push(a);
        self
    }

    /// Adds the operand `%name`.
    pub fn operand(mut self, name: impl Into<String>) -> Op {
        self.operands.push(name.into());
        self
    }

    /// Adds the successor `^label(args)`.
    pub fn succ(mut self, label: impl Into<String>, args: &[&str]) -> Op {
        let args = args.iter().map(|a| a.to_string()).collect();
        self.succs.push(Succ::new(label, args));
        self
    }

    /// Adds a region.
    pub fn region(mut self, r: Region) -> Op {
        self.regions.push(r);
        self
    }
}

impl Block {
    /// A block labelled `label`, with no arguments and no ops yet.
    pub fn new(label: impl Into<String>) -> Block {
        Block {
            label: label.into(),
            params: Vec::new(),
            ops: Vec::new(),
        }
    }

    /// Adds the argument `%name: ty`.
    pub fn param(mut self, name: impl Into<String>, ty: Type) -> Block {
        self.params.push(Def::new(name, ty));
        self
    }

    /// Adds an op at the end.
    pub fn op(mut self, op: Op) -> Block {
        self.ops.push(op);
        self
    }
}

impl Region {
    /// A region of these blocks.
    pub fn new(blocks: Vec<Block>) -> Region {
        Region { blocks }
    }
}

impl Func {
    /// A function with symbol `name`, no parameters, no results and no
    /// blocks yet.
    pub fn new(name: impl Into<String>) -> Func {
        Func {
            name: name.into(),
            params: Vec::new(),
            results: Vec::new(),
            body: Region::default(),
        }
    }

    /// Adds the parameter `%name: ty`.
    pub fn param(mut self, name: impl Into<String>, ty: Type) -> Func {
        self.params.push(Def::new(name, ty));
        self
    }

    /// Adds a result type.
    pub fn result(mut self, ty: Type) -> Func {
        self.results.push(ty);
        self
    }

    /// Adds a block at the end of the body.
    pub fn block(mut self, b: Block) -> Func {
        self.body.blocks.push(b);
        self
    }
}

impl Module {
    /// An empty module with an empty location table.
    pub fn new() -> Module {
        Module::default()
    }

    /// Adds a function at the end.
    pub fn func(mut self, f: Func) -> Module {
        self.items.push(Item::Func(f));
        self
    }
}
