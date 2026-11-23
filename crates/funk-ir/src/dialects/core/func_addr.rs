//! The address of a function: `funcaddr` (`decodeFuncAddr` in
//! `lean/Fir/Core/FuncAddrText.lean`, `funcAddrValue` in
//! `lean/Fir/Core/FuncAddr.lean`, `Op.Valid` and `Op.symbolRefs` in
//! `lean/Fir/Core/Validation.lean`; #235).
//!
//! `funcaddr` has one attribute, the symbol of a function, and no operands,
//! as in `%p: ptr = funcaddr @f`, and defines a pointer to that function's
//! allocation, which has no units (the human's ruling of 2026-11-19 on #235,
//! Q1). Validation requires that the symbol name a function of the op's own
//! table, as `call` names its callee, and that the result be a pointer of
//! memory 0. It is pure: it is never UB, and its result is never poison.

use super::type_list;
use super::types::{CoreType, core_type};
use crate::Attr;
use crate::effects::Effects;
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};
use crate::text::print_symbol;

/// The function's symbol: the one attribute.
fn attrs<'a>(op: &OpTypes<'a>) -> Result<&'a str, String> {
    match op.attrs {
        [Attr::Sym(s)] => Ok(s),
        _ => Err("funcaddr takes one attribute, a function's symbol, such as @f".into()),
    }
}

/// The memory of the pointer that `funcaddr` defines, when its operands
/// and result decode.
fn shape(op: &OpTypes<'_>) -> Option<u32> {
    match (op.operands, op.results) {
        ([], [r]) => match core_type(r) {
            Some(CoreType::Ptr(n)) => Some(n),
            _ => None,
        },
        _ => None,
    }
}

/// `%p: ptr = funcaddr @f`.
pub(super) struct FuncAddr;

impl OpSpec for FuncAddr {
    fn name(&self) -> &str {
        "funcaddr"
    }

    /// The symbol is one the op refers to, so the verifier checks that it
    /// names a function of the op's table (`Op.symbolRefs`).
    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        let s = attrs(op)?;
        match shape(op) {
            Some(_) => Ok(OpShape {
                symbols: vec![s.to_string()],
                ..OpShape::default()
            }),
            None => Err(format!(
                "funcaddr takes no operands and defines a pointer, not {} -> {}",
                type_list(op.operands),
                type_list(op.results)
            )),
        }
    }

    /// The result is a pointer of memory 0, where every function's
    /// allocation is.
    fn check(&self, _cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        let s = attrs(op)?;
        match shape(op).ok_or("funcaddr does not decode")? {
            0 => Ok(()),
            n => Err(format!(
                "funcaddr {} gives a pointer of memory 0, where functions are, but its result \
                 is a pointer of memory {n}",
                print_symbol(s)
            )),
        }
    }

    /// Pure (`Core.Op.effects`).
    fn effects(&self, _op: &OpTypes<'_>) -> Effects {
        Effects::PURE
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Type;
    use crate::dialects::core::{int_type, ptr_type};

    fn decode(attrs: &[Attr], operands: &[Type], results: &[Type]) -> Result<OpShape, String> {
        FuncAddr.decode(&OpTypes {
            attrs,
            operands,
            results,
        })
    }

    fn f() -> [Attr; 1] {
        [Attr::Sym("f".into())]
    }

    #[test]
    fn a_pointer_result_decodes_in_every_memory_and_refers_to_its_function() {
        for n in [0, 1, 7] {
            assert_eq!(decode(&f(), &[], &[ptr_type(n)]).unwrap().symbols, ["f"]);
        }
    }

    #[test]
    fn every_other_shape_does_not_decode() {
        let (p, i64) = (ptr_type(0), int_type(64));
        for (operands, results) in [
            (vec![], vec![i64.clone()]),
            (vec![], vec![]),
            (vec![], vec![p.clone(), p.clone()]),
            (vec![p.clone()], vec![p.clone()]),
            (vec![i64.clone()], vec![p.clone()]),
        ] {
            let e = decode(&f(), &operands, &results).unwrap_err();
            assert!(e.starts_with("funcaddr takes no operands"), "{e}");
        }
    }

    #[test]
    fn the_attribute_is_one_symbol() {
        let p = [ptr_type(0)];
        for attrs in [
            vec![],
            vec![Attr::Sym("f".into()), Attr::Sym("g".into())],
            vec![Attr::Sym("f".into()), Attr::int(0)],
            vec![Attr::int(0)],
            vec![Attr::word("f")],
        ] {
            let e = decode(&attrs, &[], &p).unwrap_err();
            assert!(e.starts_with("funcaddr takes one attribute"), "{e}");
        }
    }

    #[test]
    fn funcaddr_is_pure() {
        let op = OpTypes {
            attrs: &f(),
            operands: &[],
            results: &[ptr_type(0)],
        };
        assert_eq!(FuncAddr.effects(&op), Effects::PURE);
    }
}
