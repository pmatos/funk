//! The address of a global: `globaladdr` (`decodeGlobalAddr` in
//! `lean/Fir/Core/GlobalAddrText.lean`, `globalAddrValue` in
//! `lean/Fir/Core/GlobalAddr.lean`, `Op.Valid` in
//! `lean/Fir/Core/Validation.lean`; #237).
//!
//! `globaladdr` has one attribute, the symbol of a global, and no operands,
//! as in `%p: ptr = globaladdr @msg`, and defines a pointer to the first
//! unit of that global's allocation. Validation requires that the symbol
//! name a global of the op's own table, as `call` names its callee, and
//! that the result be a pointer of the global's memory. It is pure: it is
//! never UB, and its result is never poison.

use super::type_list;
use super::types::{CoreType, core_type};
use crate::Attr;
use crate::effects::Effects;
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};
use crate::text::print_symbol;

/// The global's symbol: the one attribute.
fn attrs<'a>(op: &OpTypes<'a>) -> Result<&'a str, String> {
    match op.attrs {
        [Attr::Sym(s)] => Ok(s),
        _ => Err("globaladdr takes one attribute, a global's symbol, such as @msg".into()),
    }
}

/// The memory of the pointer that `globaladdr` defines, when its operands
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

/// `%p: ptr = globaladdr @msg`.
pub(super) struct GlobalAddr;

impl OpSpec for GlobalAddr {
    fn name(&self) -> &str {
        "globaladdr"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        attrs(op)?;
        match shape(op) {
            Some(_) => Ok(OpShape::default()),
            None => Err(format!(
                "globaladdr takes no operands and defines a pointer, not {} -> {}",
                type_list(op.operands),
                type_list(op.results)
            )),
        }
    }

    /// The symbol names a global of the op's own table, of the result's
    /// memory.
    fn check(&self, cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        let s = attrs(op)?;
        let n = shape(op).ok_or("globaladdr does not decode")?;
        let sym = print_symbol(s);
        let Some(g) = cx.symbols.global(s) else {
            return Err(format!("globaladdr {sym} names no global of its table"));
        };
        if g.memory != u64::from(n) {
            return Err(format!(
                "globaladdr {sym} is a global of memory {}, but its result is a pointer of \
                 memory {n}",
                g.memory
            ));
        }
        Ok(())
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
        GlobalAddr.decode(&OpTypes {
            attrs,
            operands,
            results,
        })
    }

    fn msg() -> [Attr; 1] {
        [Attr::Sym("msg".into())]
    }

    #[test]
    fn a_pointer_result_decodes_in_every_memory() {
        for n in [0, 1, 7] {
            assert!(decode(&msg(), &[], &[ptr_type(n)]).is_ok());
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
            let e = decode(&msg(), &operands, &results).unwrap_err();
            assert!(e.starts_with("globaladdr takes no operands"), "{e}");
        }
    }

    #[test]
    fn the_attribute_is_one_symbol() {
        let p = [ptr_type(0)];
        for attrs in [
            vec![],
            vec![Attr::Sym("msg".into()), Attr::Sym("tbl".into())],
            vec![Attr::Sym("msg".into()), Attr::int(0)],
            vec![Attr::int(0)],
            vec![Attr::word("msg")],
        ] {
            let e = decode(&attrs, &[], &p).unwrap_err();
            assert!(e.starts_with("globaladdr takes one attribute"), "{e}");
        }
    }

    #[test]
    fn globaladdr_is_pure() {
        let op = OpTypes {
            attrs: &msg(),
            operands: &[],
            results: &[ptr_type(0)],
        };
        assert_eq!(GlobalAddr.effects(&op), Effects::PURE);
    }
}
