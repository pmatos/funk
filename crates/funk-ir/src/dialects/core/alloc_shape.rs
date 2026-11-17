//! The shape of an allocation: the attributes that `alloca` writes after
//! its kind, and that `gpu.work_group_alloca` writes with no kind
//! (`decodeAlloca` in `lean/Fir/Core/AllocaText.lean`, `decodeAlloc` in
//! `lean/Fir/Gpu/Text.lean`, their rules in `Core.Op.Valid` and
//! `Gpu.Op.Valid`).
//!
//! The shape is, in order: the type, written as a type is and read with no
//! bound on its width, format or memory; the count, an integer that is not
//! negative and not 1, written only when it is not 1; and `align(A)`, with
//! `A` not negative, written only when the op gives an alignment.
//! Validation accepts a count of at least 1, an alignment that
//! [`check_align`] accepts, and a valid type: an integer, a pointer, or a
//! float (#264; the human's ruling of 2026-11-15 on #397), which takes the
//! units of its bits.

use super::align::{check_align, decode_align};
use super::types::{CoreType, FLOAT_ALIASES, MAX_MEMORY, MAX_WIDTH, alias, ptr_type};
use crate::{Attr, Int, Type};

/// The type an allocation carries, read with no bound (`Ty.decodeAny`):
/// `iN` with its digits, a float format with the digits of its exponent and
/// mantissa bits, or a pointer of a memory, with the memory's digits.
#[derive(Clone, Debug, PartialEq, Eq)]
enum AnyType {
    Int(Int),
    Float(Int, Int),
    Ptr(Int),
}

/// The memory of a pointer type, when it is at most [`MAX_MEMORY`].
fn valid_memory(n: &Int) -> Option<u32> {
    n.as_str().parse::<u32>().ok().filter(|&n| n <= MAX_MEMORY)
}

/// An integer not negative, from its canonical spelling.
fn nonneg(i: &Int) -> bool {
    !i.is_negative()
}

/// The number that `i` spells, when it fits in 32 bits.
fn small(i: &Int) -> Option<u32> {
    i.as_str().parse::<u32>().ok()
}

/// The core type that `t` is when it is valid (`Ty.Valid`): `iN` with
/// `1 <= N <= MAX_WIDTH`, `float<e,m>` with `e >= 2`, `m >= 1` and
/// `1 + e + m <= MAX_WIDTH`, or `ptr<N>` with `N <= MAX_MEMORY`.
fn valid(t: &AnyType) -> Option<CoreType> {
    match t {
        AnyType::Int(w) => small(w)
            .filter(|w| (1..=MAX_WIDTH).contains(w))
            .map(CoreType::Int),
        AnyType::Float(e, m) => {
            let (e, m) = (small(e)?, small(m)?);
            (e >= 2 && m >= 1 && u64::from(e) + u64::from(m) < u64::from(MAX_WIDTH))
                .then_some(CoreType::Float { e, m })
        }
        AnyType::Ptr(n) => valid_memory(n).map(CoreType::Ptr),
    }
}

/// Reads a core type as the spec writes it, with no bound on a width, a
/// format or a memory, or `None` when the attribute is not one.
fn decode_any(a: &Attr) -> Option<AnyType> {
    match a {
        Attr::Word(w) if w == "ptr" => Some(AnyType::Ptr(Int::from(0i128))),
        Attr::Word(w) => match w.strip_prefix('i') {
            Some(digits) => {
                let i = Int::parse(digits)?;
                nonneg(&i).then_some(AnyType::Int(i))
            }
            None => FLOAT_ALIASES
                .iter()
                .find(|f| f.0 == w)
                .map(|f| AnyType::Float(Int::from(i128::from(f.1)), Int::from(i128::from(f.2)))),
        },
        Attr::App(h, args) if h == "float" => match args.as_slice() {
            [Attr::Int(e), Attr::Int(m)] if nonneg(e) && nonneg(m) => {
                let format = small(e).zip(small(m));
                format
                    .and_then(|(e, m)| alias(e, m))
                    .is_none()
                    .then(|| AnyType::Float(e.clone(), m.clone()))
            }
            _ => None,
        },
        Attr::App(h, args) if h == "ptr" => match args.as_slice() {
            [Attr::Int(n)] if nonneg(n) && n.as_str() != "0" => Some(AnyType::Ptr(n.clone())),
            _ => None,
        },
        _ => None,
    }
}

/// The attributes of an allocation after its kind: its type, its count and
/// its alignment.
pub(super) struct Shape<'a> {
    ty: AnyType,
    pub(super) count: Option<&'a Int>,
    pub(super) align: Option<&'a Int>,
}

impl Shape<'_> {
    /// The type of its values, when that type is valid.
    pub(super) fn element(&self) -> Option<CoreType> {
        valid(&self.ty)
    }
}

/// Reads the attributes of an allocation after its kind, or `None` when
/// they do not decode.
pub(super) fn shape(attrs: &[Attr]) -> Option<Shape<'_>> {
    let [ty, rest @ ..] = attrs else {
        return None;
    };
    let ty = decode_any(ty)?;
    let (count, rest) = match rest {
        [Attr::Int(c), rest @ ..] if nonneg(c) && c.as_str() != "1" => (Some(c), rest),
        [Attr::Int(_), ..] => return None,
        rest => (None, rest),
    };
    let align = decode_align(rest)?;
    Some(Shape { ty, count, align })
}

/// Whether the attributes of an allocation after its kind decode.
pub(crate) fn shape_decodes(attrs: &[Attr]) -> bool {
    shape(attrs).is_some()
}

/// The rules of an allocation beyond its kind, for the op `op` whose
/// attributes after its kind are `attrs`: at least one value, an alignment
/// that `check_align` accepts, and a valid type (`Core.Op.Valid`,
/// `Gpu.Op.Valid`). Attributes that do not decode break no rule here:
/// decoding reports them.
pub(crate) fn check_shape(op: &str, attrs: &[Attr]) -> Result<(), String> {
    shape(attrs).map_or(Ok(()), |p| check_shape_of(op, &p))
}

/// The type an allocation carries, as it is written.
fn written(t: &AnyType) -> String {
    match t {
        AnyType::Int(w) => format!("i{}", w.as_str()),
        AnyType::Float(e, m) => match small(e).zip(small(m)).and_then(|(e, m)| alias(e, m)) {
            Some(name) => name.to_string(),
            None => format!("float({}, {})", e.as_str(), m.as_str()),
        },
        AnyType::Ptr(n) if n.as_str() == "0" => "ptr".to_string(),
        AnyType::Ptr(n) => format!("ptr({})", n.as_str()),
    }
}

/// The rules of an allocation beyond its kind, on its decoded shape.
pub(super) fn check_shape_of(op: &str, p: &Shape<'_>) -> Result<(), String> {
    if p.count.is_some_and(|c| c.as_str() == "0") {
        return Err(format!("{op} allocates at least one value, not 0"));
    }
    if let Some(a) = p.align {
        check_align(op, a.as_str())?;
    }
    if p.element().is_some() {
        return Ok(());
    }
    let kind = match p.ty {
        AnyType::Int(_) => "integer",
        AnyType::Float(..) => "float",
        AnyType::Ptr(_) => "pointer",
    };
    Err(format!(
        "{op} allocates a valid {kind} type, not {}",
        written(&p.ty)
    ))
}

/// The type that an allocation whose attributes after its kind are
/// `attrs` allocates values of, when that is a valid pointer type, whose
/// memory the data layout must declare (`Core.Op.attrTypes`,
/// `Gpu.Op.attrTypes`). An integer or float type names no memory, and a
/// type that is not valid breaks the op's own rule.
pub(crate) fn shape_attr_types(attrs: &[Attr]) -> Vec<Type> {
    shape(attrs).map(|p| shape_types(&p)).unwrap_or_default()
}

/// The type that a decoded shape allocates values of, when that is a valid
/// pointer type.
pub(super) fn shape_types(p: &Shape<'_>) -> Vec<Type> {
    match p.element() {
        Some(CoreType::Ptr(n)) => vec![ptr_type(n)],
        _ => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn float(e: i128, m: i128) -> Attr {
        Attr::App("float".into(), vec![Attr::int(e), Attr::int(m)])
    }

    #[test]
    fn every_valid_float_format_is_an_element() {
        for (attr, e, m) in [
            (Attr::word("f16"), 5, 10),
            (Attr::word("bf16"), 8, 7),
            (Attr::word("f32"), 8, 23),
            (Attr::word("f64"), 11, 52),
            (Attr::word("f128"), 15, 112),
            (float(2, 1), 2, 1),
            (float(8, 16_777_206), 8, 16_777_206),
        ] {
            let p = shape(std::slice::from_ref(&attr)).unwrap();
            assert_eq!(p.element(), Some(CoreType::Float { e, m }), "{attr:?}");
            assert_eq!(check_shape_of("alloca", &p), Ok(()), "{attr:?}");
            assert!(shape_types(&p).is_empty(), "{attr:?}");
        }
    }

    #[test]
    fn an_invalid_float_format_is_not() {
        for (attr, shown) in [
            (float(1, 1), "float(1, 1)"),
            (float(2, 0), "float(2, 0)"),
            (float(8, 16_777_207), "float(8, 16777207)"),
            (float(1 << 40, 1), "float(1099511627776, 1)"),
        ] {
            let p = shape(std::slice::from_ref(&attr)).unwrap();
            assert_eq!(p.element(), None, "{attr:?}");
            assert_eq!(
                check_shape_of("alloca", &p),
                Err(format!("alloca allocates a valid float type, not {shown}")),
                "{attr:?}"
            );
        }
        assert!(shape(&[float(8, 23)]).is_none());
        assert!(shape(&[float(-1, 3)]).is_none());
    }
}
