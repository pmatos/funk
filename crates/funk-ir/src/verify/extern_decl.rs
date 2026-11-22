//! The rules of an external declaration (`Extern.Valid` in
//! `lean/Fir/Validation/Signature.lean`, ADR-2026-11-09-1547), in the order
//! of `Extern.problems`: its parameters are named by distinct names, its
//! types are valid, it holds its attributes in the form the text reads, and
//! the dialect of each parameter's and result's type allows its attributes.
//! Its parameters may end in `...`.

use std::collections::HashSet;

use super::Diagnostic;
use super::items::value_ref;
use crate::ir::names::is_name;
use crate::ir::{Extern, attrs_trimmed};
use crate::registry::{Registry, TypeCheck};

/// Checks the external declaration `e`.
pub(super) fn check(e: &Extern, reg: &Registry, out: &mut Vec<Diagnostic>) {
    let at = |message: String| Diagnostic::at_block(&e.name, None, message);
    for p in e.params.iter().filter(|p| !is_name(&p.name)) {
        out.push(at(format!(
            "the parameter {} is not a name",
            value_ref(&p.name)
        )));
    }
    let mut seen = HashSet::new();
    for p in &e.params {
        if !seen.insert(p.name.as_str()) {
            out.push(at(format!(
                "the declaration defines {} more than once",
                value_ref(&p.name)
            )));
        }
    }
    if e.types().any(|t| reg.check_type(t) != TypeCheck::Valid) {
        out.push(at("a type of the declaration is not valid".to_string()));
    }
    if !attrs_trimmed(&e.param_attrs, e.params.len())
        || !attrs_trimmed(&e.result_attrs, e.results.len())
    {
        out.push(at(
            "the declaration holds the attributes of its parameters or results in another form than the text reads".to_string(),
        ));
    }
    for (i, p) in e.params.iter().enumerate() {
        if !reg.sig_attrs(&p.ty, e.param_attrs_of(i)) {
            out.push(at(format!(
                "the attributes of parameter {} are not ones its type allows",
                value_ref(&p.name)
            )));
        }
    }
    for (i, t) in e.results.iter().enumerate() {
        if !reg.sig_attrs(t, e.result_attrs_of(i)) {
            out.push(at(
                "the attributes of a result of the declaration are not ones its type allows"
                    .to_string(),
            ));
        }
    }
}
