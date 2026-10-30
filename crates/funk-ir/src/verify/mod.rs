//! The verifier: every rule of `Module.Valid` (`lean/Fir/Validation/`), with
//! each dialect's own rules through the registry.
//!
//! A module that parsed can still be invalid, and the IR can hold what no
//! text can, such as an ill-typed op that a pass made, so the verifier checks
//! types too. It reports every broken rule it finds, each as a [`Diagnostic`]
//! that names where the rule broke and carries the IR location of the op.

mod cfg;
mod func;
mod locs;
mod ops;

use std::collections::HashSet;
use std::fmt;

use crate::ir::{LocRef, Module};
use crate::registry::Registry;
use crate::text::print_symbol;

/// A broken rule of validation, and where in the module it broke.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    /// What is wrong.
    pub message: String,
    /// The symbol of the item, when the rule is about one.
    pub func: Option<String>,
    /// The label of the block, when the rule is about one.
    pub block: Option<String>,
    /// The index of the op in its block, when the rule is about one.
    pub op: Option<usize>,
    /// The IR location: the op's location reference, or for a block the
    /// reference of its first op.
    pub loc: Option<LocRef>,
}

impl Diagnostic {
    fn module(message: String) -> Diagnostic {
        Diagnostic {
            message,
            func: None,
            block: None,
            op: None,
            loc: None,
        }
    }

    /// Where the rule broke, as `@f ^block op N`, with the parts that apply.
    pub fn path(&self) -> Vec<String> {
        let mut path = Vec::new();
        if let Some(func) = &self.func {
            path.push(print_symbol(func));
        }
        if let Some(block) = &self.block {
            path.push(format!("^{block}"));
        }
        if let Some(op) = self.op {
            path.push(format!("op {op}"));
        }
        path
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut path = self.path();
        if let Some(loc) = self.loc {
            path.push(format!("at {loc}"));
        }
        if path.is_empty() {
            f.write_str(&self.message)
        } else {
            write!(f, "{}: {}", path.join(" "), self.message)
        }
    }
}

/// Checks `m` against every rule of validation. An empty list means that
/// the module is valid.
pub fn verify(m: &Module, reg: &Registry) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    for item in &m.items {
        if !seen.insert(item.name()) {
            let mut d = Diagnostic::module(format!(
                "the symbol {} names more than one item",
                print_symbol(item.name())
            ));
            d.func = Some(item.name().to_string());
            out.push(d);
        }
    }
    let keys: HashSet<LocRef> = m.locs.entries.iter().map(|(r, _)| *r).collect();
    out.extend(
        locs::check(&m.locs, &keys)
            .into_iter()
            .map(Diagnostic::module),
    );
    let symbols = m.symbols();
    for f in m.funcs() {
        func::check(
            f,
            &func::Context {
                symbols: &symbols,
                locs: &keys,
                reg,
            },
            &mut out,
        );
    }
    out
}
