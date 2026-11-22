//! External declarations (`Extern` in `lean/Fir/Syntax/Module.lean`,
//! ADR-2026-11-09-1547): functions that funk did not compile, which a module
//! names by a symbol and a signature, with no body.

use super::attr::{Attr, Type};
use super::module::Def;

/// An external declaration: an item of the core's kind `extern`, written as
/// a function's header with an empty body,
/// `extern @printf(%fmt: ptr, ...) -> i32 {` and `}`. Its parameters and
/// results carry attributes as a [`Func`](super::Func)'s do, held the same
/// way, and its parameters may end in `...`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Extern {
    /// The declaration's symbol, without `@`. Any string.
    pub name: String,
    /// The parameters, each named as the text writes it.
    pub params: Vec<Def>,
    /// The result types.
    pub results: Vec<Type>,
    /// The attributes of each parameter, with the empty lists at the end
    /// left out (`Extern.paramAttrs`).
    pub param_attrs: Vec<Vec<Attr>>,
    /// The attributes of each result, held as the parameters' are.
    pub result_attrs: Vec<Vec<Attr>>,
    /// Whether the parameters end in `...`.
    pub variadic: bool,
}

impl Extern {
    /// The declaration `@name` with no parameters or results.
    pub fn new(name: impl Into<String>) -> Extern {
        Extern {
            name: name.into(),
            params: Vec::new(),
            results: Vec::new(),
            param_attrs: Vec::new(),
            result_attrs: Vec::new(),
            variadic: false,
        }
    }

    /// The attributes of the parameter at `i`: none past those held.
    pub fn param_attrs_of(&self, i: usize) -> &[Attr] {
        self.param_attrs.get(i).map_or(&[], Vec::as_slice)
    }

    /// The attributes of the result at `i`: none past those held.
    pub fn result_attrs_of(&self, i: usize) -> &[Attr] {
        self.result_attrs.get(i).map_or(&[], Vec::as_slice)
    }

    /// Every type that the declaration states: its parameters' types, then
    /// its results (`Extern.types`).
    pub fn types(&self) -> impl Iterator<Item = &Type> {
        self.params.iter().map(|p| &p.ty).chain(&self.results)
    }
}
