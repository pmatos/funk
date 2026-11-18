//! The field address: `fieldaddr` (`decodeFieldAddr` in
//! `lean/Fir/Core/FieldAddrText.lean`, `fieldAddrValue` and `elemAddrValue`
//! in `lean/Fir/Core/FieldAddr.lean`, `Op.Valid` in
//! `lean/Fir/Core/Validation.lean`; #236).
//!
//! `fieldaddr` has two attributes, the symbol of an aggregate's layout and
//! the number of one of its fields, counted from 0, as in
//! `%q: ptr = fieldaddr @pair 1 %p`. It takes a pointer of `ptr<N>`, and an
//! integer of any width after it, the index of an element of a repeated
//! field, as in `%e: ptr = fieldaddr @row 0 %p, %k`, and defines a pointer of
//! the same memory: the pointer moved by the field's offset, plus the index,
//! read as signed, times the units from one element to the next. Validation
//! requires that the symbol name a layout of the op's table in the memory
//! of its pointer, that the field be one of the layout's, and that only a
//! repeated field take an index. It is pure: it is never UB, and its result
//! is poison only for a poison operand.

use super::type_list;
use super::types::{CoreType, core_type};
use crate::effects::Effects;
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};
use crate::text::print_symbol;
use crate::{Attr, Int};

/// The layout's symbol and the field's number: the two attributes, the
/// number not negative.
fn attrs<'a>(op: &OpTypes<'a>) -> Result<(&'a str, &'a Int), String> {
    match op.attrs {
        [Attr::Sym(s), Attr::Int(i)] if !i.is_negative() => Ok((s, i)),
        _ => Err(
            "fieldaddr takes two attributes, a layout's symbol and a field's number, \
             such as @pair 1"
                .into(),
        ),
    }
}

/// The memory of the pointer that `fieldaddr` takes, and whether it takes an
/// index too, when its operands and result decode.
fn shape(op: &OpTypes<'_>) -> Option<(u32, bool)> {
    let indexed = match op.operands {
        [_] => false,
        [_, k] if matches!(core_type(k), Some(CoreType::Int(_))) => true,
        _ => return None,
    };
    match (op.operands.first().and_then(core_type), op.results) {
        (Some(CoreType::Ptr(n)), [r]) if core_type(r) == Some(CoreType::Ptr(n)) => {
            Some((n, indexed))
        }
        _ => None,
    }
}

/// `%q: ptr = fieldaddr @pair 1 %p` and `%e: ptr = fieldaddr @row 0 %p, %k`.
pub(super) struct FieldAddr;

impl OpSpec for FieldAddr {
    fn name(&self) -> &str {
        "fieldaddr"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        attrs(op)?;
        match shape(op) {
            Some(_) => Ok(OpShape::default()),
            None => Err(format!(
                "fieldaddr takes a pointer, and an integer index, and defines a pointer of the \
                 same memory, not {} -> {}",
                type_list(op.operands),
                type_list(op.results)
            )),
        }
    }

    /// The layout is one of the table's, of the pointer's memory, and has
    /// the field, which is repeated when the op takes an index.
    fn check(&self, cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        let (s, i) = attrs(op)?;
        let (n, indexed) = shape(op).ok_or("fieldaddr does not decode")?;
        let sym = print_symbol(s);
        let Some(a) = cx.symbols.layout(s) else {
            return Err(format!("fieldaddr {sym} names no aggregate's layout"));
        };
        if a.memory != u64::from(n) {
            return Err(format!(
                "fieldaddr {sym} is a layout of memory {}, but its pointer is of memory {n}",
                a.memory
            ));
        }
        let field = i
            .as_str()
            .parse::<usize>()
            .ok()
            .and_then(|i| a.fields.get(i));
        match field {
            None => Err(format!(
                "fieldaddr {sym} {} names no field: {sym} has {} fields",
                i.as_str(),
                a.fields.len()
            )),
            Some(f) if indexed && f.count.is_none() => Err(format!(
                "fieldaddr {sym} {} takes an index, but the field is not repeated",
                i.as_str()
            )),
            Some(_) => Ok(()),
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
    use crate::dialects::core::{float_type, int_type, ptr_type};

    fn decode(attrs: &[Attr], operands: &[Type], results: &[Type]) -> Result<OpShape, String> {
        FieldAddr.decode(&OpTypes {
            attrs,
            operands,
            results,
        })
    }

    fn pair() -> [Attr; 2] {
        [Attr::Sym("pair".into()), Attr::int(1)]
    }

    #[test]
    fn a_pointer_and_an_optional_index_decode_in_every_memory() {
        for n in [0, 1, 7] {
            assert!(decode(&pair(), &[ptr_type(n)], &[ptr_type(n)]).is_ok());
            for w in [1, 8, 64, 128] {
                let ops = [ptr_type(n), int_type(w)];
                assert!(decode(&pair(), &ops, &[ptr_type(n)]).is_ok());
            }
        }
    }

    #[test]
    fn every_other_shape_does_not_decode() {
        let (p, p1, i64, f32) = (ptr_type(0), ptr_type(1), int_type(64), float_type(8, 23));
        for (operands, results) in [
            (vec![p.clone()], vec![p1.clone()]),
            (vec![p.clone()], vec![i64.clone()]),
            (vec![i64.clone()], vec![p.clone()]),
            (vec![p.clone(), f32.clone()], vec![p.clone()]),
            (vec![p.clone(), p.clone()], vec![p.clone()]),
            (vec![p.clone(), i64.clone(), i64.clone()], vec![p.clone()]),
            (vec![], vec![p.clone()]),
            (vec![p.clone()], vec![]),
        ] {
            let e = decode(&pair(), &operands, &results).unwrap_err();
            assert!(e.starts_with("fieldaddr takes a pointer"), "{e}");
        }
    }

    #[test]
    fn the_attributes_are_a_symbol_and_a_field_number() {
        let p = [ptr_type(0)];
        for attrs in [
            vec![],
            vec![Attr::Sym("pair".into())],
            vec![Attr::int(1), Attr::Sym("pair".into())],
            vec![Attr::Sym("pair".into()), Attr::int(-1)],
            vec![Attr::Sym("pair".into()), Attr::int(1), Attr::int(2)],
            vec![Attr::word("pair"), Attr::int(1)],
        ] {
            let e = decode(&attrs, &p, &p).unwrap_err();
            assert!(e.starts_with("fieldaddr takes two attributes"), "{e}");
        }
    }

    #[test]
    fn fieldaddr_is_pure() {
        let op = OpTypes {
            attrs: &pair(),
            operands: &[ptr_type(0)],
            results: &[ptr_type(0)],
        };
        assert_eq!(FieldAddr.effects(&op), Effects::PURE);
    }
}
