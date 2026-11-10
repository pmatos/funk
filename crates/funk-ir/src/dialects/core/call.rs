//! Calls: `call` (`lean/Fir/Core/Ops.lean`, `Op.decode` in
//! `lean/Fir/Core/Text.lean`, `Op.symbolRefs` and `Op.Valid` in
//! `lean/Fir/Core/Validation.lean`).
//!
//! `call` has one attribute, its callee's symbol (H3,
//! ADR-2026-10-29-2012), as in `%s: i32 = call @sum %ten @6`, and any number
//! of operands and results of core types, none included
//! (ADR-2026-10-30-0816). It decodes at any types, so a call that does not
//! match its callee still parses; validation rejects it. The callee may be
//! any function of the module, the caller itself included.

use super::type_list;
use super::types::core_type;
use crate::effects::Effects;
use crate::ir::{Attr, Type};
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};
use crate::text::print_symbol;

/// The callee of a call: its one attribute, a symbol.
fn callee<'a>(op: &OpTypes<'a>) -> Result<&'a str, String> {
    match op.attrs {
        [Attr::Sym(f)] => Ok(f),
        _ => Err("call takes one attribute, its callee's symbol, such as @f".into()),
    }
}

/// The first type of `tys` that is not a core type.
fn foreign(tys: &[Type]) -> Option<&Type> {
    tys.iter().find(|t| core_type(t).is_none())
}

/// `%r: i32 = call @f %a, %b`.
pub(super) struct Call;

impl OpSpec for Call {
    fn name(&self) -> &str {
        "call"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        let f = callee(op)?;
        if let Some(t) = foreign(op.operands) {
            return Err(format!("call passes values of core types, not {t}"));
        }
        if let Some(t) = foreign(op.results) {
            return Err(format!("call defines values of core types, not {t}"));
        }
        Ok(OpShape {
            symbols: vec![f.to_string()],
            ..OpShape::default()
        })
    }

    /// The callee's signature is what the call passes and defines: `call f
    /// ts rs` is valid when `ctx.symbols f = some ⟨ts, rs⟩`. A callee that
    /// names no function breaks this rule too, as it does in the spec.
    fn check(&self, cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        let f = callee(op)?;
        let (passes, defines) = (type_list(op.operands), type_list(op.results));
        let sym = print_symbol(f);
        match cx.symbols.func_type(f) {
            Some(t) if t.params == op.operands && t.results == op.results => Ok(()),
            Some(t) => Err(format!(
                "call {sym} passes {passes} and defines {defines}, but {sym} takes {} and \
                 returns {}",
                type_list(&t.params),
                type_list(&t.results)
            )),
            None => Err(format!(
                "call {sym} passes {passes} and defines {defines}, but no function is \
                 named {sym}"
            )),
        }
    }

    /// Empty: `call`'s own rule only runs its callee. A call has its
    /// callee's effects too, which [`Summaries`](crate::Summaries) adds
    /// (`Core.Op.effects`, `SymbolTable.opEffects`).
    fn effects(&self, _op: &OpTypes<'_>) -> Effects {
        Effects::PURE
    }

    /// `call @f` calls `@f`, as `Core.Op.callTarget?` says.
    fn callee(&self, op: &OpTypes<'_>) -> Option<String> {
        callee(op).ok().map(str::to_string)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialects::core::int_type;

    fn decode(attrs: &[Attr], operands: &[Type], results: &[Type]) -> Result<OpShape, String> {
        Call.decode(&OpTypes {
            attrs,
            operands,
            results,
        })
    }

    #[test]
    fn call_decodes_at_any_core_types_as_the_spec_reads_it() {
        let f = [Attr::Sym("f".into())];
        let (i1, i7, ptr) = (int_type(1), int_type(7), Type::word("ptr"));
        for (operands, results) in [
            (vec![], vec![]),
            (vec![i1.clone()], vec![]),
            (vec![], vec![i7.clone(), i1.clone()]),
            (vec![i7.clone(); 9], vec![ptr.clone()]),
        ] {
            let shape = decode(&f, &operands, &results).unwrap();
            assert_eq!(shape.symbols, ["f"]);
            assert!(!shape.terminator && shape.successors == 0);
        }
        let quoted = decode(&[Attr::Sym("1".into())], &[], &[]).unwrap();
        assert_eq!(quoted.symbols, ["1"]);
    }

    #[test]
    fn call_names_its_callee_by_one_symbol_and_uses_core_types() {
        let i8 = int_type(8);
        for attrs in [
            vec![],
            vec![Attr::word("f")],
            vec![Attr::Str("f".into())],
            vec![Attr::Sym("f".into()), Attr::Sym("g".into())],
            vec![Attr::Sym("f".into()), Attr::word("nsw")],
        ] {
            let why = decode(&attrs, std::slice::from_ref(&i8), &[]).unwrap_err();
            assert!(why.starts_with("call takes one attribute"), "{why}");
        }
        let f = [Attr::Sym("f".into())];
        let tok = Type::word("toy.tok");
        let why = decode(&f, &[i8.clone(), tok.clone()], &[]).unwrap_err();
        assert_eq!(why, "call passes values of core types, not toy.tok");
        let why = decode(&f, &[], &[i8, tok]).unwrap_err();
        assert_eq!(why, "call defines values of core types, not toy.tok");
    }
}
