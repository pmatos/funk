//! Calls between the functions of a generated module (`call`, #20).
//!
//! Every function's symbol and type are chosen before any body, so a call
//! may name any function of the module: one before its caller, one after
//! it, or the caller itself, which makes direct and mutual recursion. A
//! call passes a value of the right type for each of its callee's
//! parameters, values in scope or new ones, and defines one new value for
//! each of its callee's results: none, one or several.

use super::blocks::value;
use super::{Body, Rng, Widths, width};
use crate::dialects::core::int_type;
use crate::ir::{Attr, FuncType, Op};

/// A function of the module: its symbol and its type.
pub(super) struct Callee {
    pub name: String,
    pub ty: FuncType,
}

/// The function `name`, with zero to three parameters and zero to three
/// results, of any widths.
pub(super) fn signature(rng: &mut Rng, name: String, widths: Widths) -> Callee {
    let types = |rng: &mut Rng| -> Vec<_> {
        (0..rng.below(4))
            .map(|_| int_type(width(rng, widths)))
            .collect()
    };
    let params = types(rng);
    let results = types(rng);
    Callee {
        name,
        ty: FuncType { params, results },
    }
}

/// Adds a `call` of a function of the module to the block, and its
/// results to the values in scope.
pub(super) fn call(rng: &mut Rng, body: &mut Body<'_>) {
    let callee = rng.pick(body.funcs);
    let args: Vec<String> = callee
        .ty
        .params
        .iter()
        .map(|t| value(rng, body, t))
        .collect();
    let mut op = Op::new("call", *rng.pick(body.keys)).attr(Attr::Sym(callee.name.clone()));
    for a in args {
        op = op.operand(a);
    }
    for t in &callee.ty.results {
        let n = body.fresh_name(rng);
        op = op.result(n.clone(), t.clone());
        body.values.push((n, t.clone()));
    }
    body.ops.push(op);
}
