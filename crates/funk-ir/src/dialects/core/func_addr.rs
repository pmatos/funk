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

use super::symbol_addr;
use crate::effects::Effects;
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};
use crate::text::print_symbol;

/// The function's symbol and the memory of the pointer that `funcaddr`
/// defines.
fn decode<'a>(op: &OpTypes<'a>) -> Result<(&'a str, u32), String> {
    symbol_addr::decode("funcaddr", "a function's symbol, such as @f", op)
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
        let (s, _) = decode(op)?;
        Ok(OpShape {
            symbols: vec![s.to_string()],
            ..OpShape::default()
        })
    }

    /// The result is a pointer of memory 0, where every function's
    /// allocation is.
    fn check(&self, _cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        match decode(op)? {
            (_, 0) => Ok(()),
            (s, n) => Err(format!(
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
    use crate::dialects::core::ptr_type;

    #[test]
    fn funcaddr_decodes_as_an_address_of_an_item_and_is_pure() {
        symbol_addr::tests::shared_rules(&FuncAddr, "f");
    }

    #[test]
    fn funcaddr_refers_to_its_function() {
        let op = OpTypes {
            attrs: &[crate::Attr::Sym("f".into())],
            operands: &[],
            results: &[ptr_type(0)],
        };
        assert_eq!(FuncAddr.decode(&op).unwrap().symbols, ["f"]);
    }
}
