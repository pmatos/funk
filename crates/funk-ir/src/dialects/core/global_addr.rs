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

use super::symbol_addr;
use crate::effects::Effects;
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};
use crate::text::print_symbol;

/// The global's symbol and the memory of the pointer that `globaladdr`
/// defines.
fn decode<'a>(op: &OpTypes<'a>) -> Result<(&'a str, u32), String> {
    symbol_addr::decode("globaladdr", "a global's symbol, such as @msg", op)
}

/// `%p: ptr = globaladdr @msg`.
pub(super) struct GlobalAddr;

impl OpSpec for GlobalAddr {
    fn name(&self) -> &str {
        "globaladdr"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        decode(op).map(|_| OpShape::default())
    }

    /// The symbol names a global of the op's own table, of the result's
    /// memory.
    fn check(&self, cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        let (s, n) = decode(op)?;
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

    #[test]
    fn globaladdr_decodes_as_an_address_of_an_item_and_is_pure() {
        symbol_addr::tests::shared_rules(&GlobalAddr, "msg");
    }
}
