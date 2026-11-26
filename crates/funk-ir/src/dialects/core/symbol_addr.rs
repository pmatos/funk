//! What the ops that give an item's address share, `globaladdr` (#237) and
//! `funcaddr` (#235): one attribute, the item's symbol, no operands and one
//! pointer result, of any memory (`decodeGlobalAddr` and `decodeFuncAddr`).

use super::type_list;
use super::types::{CoreType, core_type};
use crate::Attr;
use crate::registry::OpTypes;

/// The symbol and the memory of the pointer result of the op `name`, whose
/// one attribute is `item`, such as "a global's symbol, such as @msg".
pub(super) fn decode<'a>(
    name: &str,
    item: &str,
    op: &OpTypes<'a>,
) -> Result<(&'a str, u32), String> {
    let [Attr::Sym(s)] = op.attrs else {
        return Err(format!("{name} takes one attribute, {item}"));
    };
    match (op.operands, op.results) {
        ([], [r]) => match core_type(r) {
            Some(CoreType::Ptr(n)) => Ok((s, n)),
            _ => Err(not_a_pointer(name, op)),
        },
        _ => Err(not_a_pointer(name, op)),
    }
}

fn not_a_pointer(name: &str, op: &OpTypes<'_>) -> String {
    format!(
        "{name} takes no operands and defines a pointer, not {} -> {}",
        type_list(op.operands),
        type_list(op.results)
    )
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use crate::Type;
    use crate::dialects::core::{int_type, ptr_type};
    use crate::effects::Effects;
    use crate::registry::{OpShape, OpSpec};

    /// Decodes `attrs`, `operands` and `results` as the op `spec`.
    fn decode(
        spec: &dyn OpSpec,
        attrs: &[Attr],
        operands: &[Type],
        results: &[Type],
    ) -> Result<OpShape, String> {
        spec.decode(&OpTypes {
            attrs,
            operands,
            results,
        })
    }

    /// Checks what both ops share, for the op `spec` and a symbol `s` of
    /// the item it names: a pointer result decodes in every memory, every
    /// other shape and list of attributes does not, and the op is pure.
    pub(in crate::dialects::core) fn shared_rules(spec: &dyn OpSpec, s: &str) {
        let name = spec.name().to_string();
        let sym = || Attr::Sym(s.into());
        for n in [0, 1, 7] {
            assert!(decode(spec, &[sym()], &[], &[ptr_type(n)]).is_ok());
        }
        let (p, i64) = (ptr_type(0), int_type(64));
        for (operands, results) in [
            (vec![], vec![i64.clone()]),
            (vec![], vec![]),
            (vec![], vec![p.clone(), p.clone()]),
            (vec![p.clone()], vec![p.clone()]),
            (vec![i64.clone()], vec![p.clone()]),
        ] {
            let e = decode(spec, &[sym()], &operands, &results).unwrap_err();
            assert!(e.starts_with(&format!("{name} takes no operands")), "{e}");
        }
        for attrs in [
            vec![],
            vec![sym(), Attr::Sym("other".into())],
            vec![sym(), Attr::int(0)],
            vec![Attr::int(0)],
            vec![Attr::word(s)],
        ] {
            let e = decode(spec, &attrs, &[], std::slice::from_ref(&p)).unwrap_err();
            assert!(e.starts_with(&format!("{name} takes one attribute")), "{e}");
        }
        let op = OpTypes {
            attrs: &[sym()],
            operands: &[],
            results: &[p],
        };
        assert_eq!(spec.effects(&op), Effects::PURE);
    }
}
