//! The core types (`lean/Fir/Core/Types.lean`, `Ty.decode` in
//! `lean/Fir/Core/Text.lean`, `Ty.Valid` in `lean/Fir/Core/Validation.lean`).
//!
//! `iN` is written `i` and `N` in decimal with no leading zeros. A width above
//! [`MAX_WIDTH`] does not decode (N3). `i0` decodes, and validation rejects
//! it. `ptr` is reserved: it decodes, and validation in M0 rejects every
//! value of type `ptr`.
//!
//! `float<e,m>` is written by its alias when it has one, `f16`, `bf16`,
//! `f32`, `f64` or `f128`, and as `float(e, m)` otherwise, so each format has
//! one spelling: `float(8, 23)` does not decode (ADR-2026-11-11-0951). A
//! format wider than [`MAX_WIDTH`] bits in all does not decode, and
//! validation rejects one with fewer than 2 exponent bits or 1 mantissa bit
//! (ADR-2026-11-11-0950).

use crate::registry::{TypeCheck, TypeSpec};
use crate::{Attr, Type};

/// The widest integer type, `i16777215`: `2^24 - 1` bits, MLIR's limit.
pub const MAX_WIDTH: u32 = (1 << 24) - 1;

/// The float formats with a name of their own, as `(name, e, m)`.
pub const FLOAT_ALIASES: [(&str, u32, u32); 5] = [
    ("f16", 5, 10),
    ("bf16", 8, 7),
    ("f32", 8, 23),
    ("f64", 11, 52),
    ("f128", 15, 112),
];

/// The head word of a float format without a name: `float(e, m)`.
const FLOAT: &str = "float";

/// A core type, decoded.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CoreType {
    /// `iN`, a bitvector of `N` bits.
    Int(u32),
    /// `float<e,m>`, with `e` exponent bits and `m` explicit mantissa bits.
    Float {
        /// The exponent bits.
        e: u32,
        /// The explicit mantissa bits.
        m: u32,
    },
    /// The reserved type `ptr`.
    Ptr,
}

/// The type `iN` with `N = width`.
pub fn int_type(width: u32) -> Type {
    Type::word(format!("i{width}"))
}

/// The alias of the format `float<e,m>`, if it has one.
fn alias(e: u32, m: u32) -> Option<&'static str> {
    FLOAT_ALIASES
        .iter()
        .find(|a| (a.1, a.2) == (e, m))
        .map(|a| a.0)
}

/// The type `float<e,m>`, written by its alias when it has one.
pub fn float_type(e: u32, m: u32) -> Type {
    match alias(e, m) {
        Some(name) => Type::word(name),
        None => Type::app(
            FLOAT,
            vec![Attr::int(i128::from(e)), Attr::int(i128::from(m))],
        ),
    }
}

/// The core type that `ty` writes, if it decodes as one.
pub fn core_type(ty: &Type) -> Option<CoreType> {
    decode(ty)?.ok()
}

/// The width of `ty` if it is `iN`.
pub fn int_width(ty: &Type) -> Option<u32> {
    match core_type(ty)? {
        CoreType::Int(w) => Some(w),
        CoreType::Float { .. } | CoreType::Ptr => None,
    }
}

/// `None` when `ty` is not a core type; an error when it looks like `iN` or
/// `float(e, m)` but is not written as the spec requires.
fn decode(ty: &Type) -> Option<Result<CoreType, String>> {
    if let Some(args) = &ty.args {
        return (ty.name == FLOAT).then(|| decode_float(args))?;
    }
    if ty.name == "ptr" {
        return Some(Ok(CoreType::Ptr));
    }
    let Some(digits) = ty.name.strip_prefix('i') else {
        let (_, e, m) = FLOAT_ALIASES.iter().find(|a| a.0 == ty.name)?;
        return Some(Ok(CoreType::Float { e: *e, m: *m }));
    };
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    if digits.len() > 1 && digits.starts_with('0') {
        return Some(Err(format!("the width of {} has a leading zero", ty.name)));
    }
    match digits.parse::<u32>() {
        Ok(w) if w <= MAX_WIDTH => Some(Ok(CoreType::Int(w))),
        _ => Some(Err(format!(
            "the width of {} is above the limit {MAX_WIDTH}",
            ty.name
        ))),
    }
}

/// `float(e, m)`: two integers, each at least 0, `1 + e + m` at most
/// [`MAX_WIDTH`], and no alias for the format. `None` when the arguments are
/// not two integers.
fn decode_float(args: &[Attr]) -> Option<Result<CoreType, String>> {
    let [Attr::Int(e), Attr::Int(m)] = args else {
        return None;
    };
    let shown = format!("{FLOAT}({}, {})", e.as_str(), m.as_str());
    if e.is_negative() || m.is_negative() {
        return Some(Err(format!("{shown} has a negative number of bits")));
    }
    let width = |i: &crate::Int| i.as_str().parse::<u32>().ok().filter(|&w| w <= MAX_WIDTH);
    let (e, m) = match (width(e), width(m)) {
        (Some(e), Some(m)) if 1 + e + m <= MAX_WIDTH => (e, m),
        _ => return Some(Err(format!("{shown} is wider than {MAX_WIDTH} bits"))),
    };
    if let Some(name) = alias(e, m) {
        return Some(Err(format!("{shown} is written {name}")));
    }
    Some(Ok(CoreType::Float { e, m }))
}

/// The core dialect's types.
pub(super) struct CoreTypes;

impl TypeSpec for CoreTypes {
    fn check(&self, ty: &Type) -> Option<TypeCheck> {
        Some(match decode(ty)? {
            Err(reason) => TypeCheck::Malformed(reason),
            Ok(CoreType::Int(0)) => {
                TypeCheck::Invalid("i0 is not a type: widths start at 1".into())
            }
            Ok(CoreType::Int(_)) => TypeCheck::Valid,
            Ok(CoreType::Float { e, m }) if e < 2 || m < 1 => TypeCheck::Invalid(format!(
                "{ty} is not a float format: it needs at least 2 exponent bits and 1 mantissa bit"
            )),
            Ok(CoreType::Float { .. }) => TypeCheck::Valid,
            Ok(CoreType::Ptr) => {
                TypeCheck::Invalid("ptr is reserved: M0 has no values of type ptr".into())
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn core_types_decode_as_the_spec_says() {
        assert_eq!(core_type(&int_type(1)), Some(CoreType::Int(1)));
        assert_eq!(
            core_type(&int_type(MAX_WIDTH)),
            Some(CoreType::Int(MAX_WIDTH))
        );
        assert_eq!(core_type(&Type::word("ptr")), Some(CoreType::Ptr));
        assert_eq!(core_type(&Type::word("i16777216")), None);
        assert_eq!(core_type(&Type::word("i032")), None);
        assert_eq!(core_type(&Type::word("u8")), None);
        assert_eq!(core_type(&Type::app("i8", vec![])), None);
        let check = |s: &str| CoreTypes.check(&Type::word(s));
        assert_eq!(check("i32"), Some(TypeCheck::Valid));
        assert!(matches!(check("i0"), Some(TypeCheck::Invalid(_))));
        assert!(matches!(check("ptr"), Some(TypeCheck::Invalid(_))));
        assert!(matches!(
            check("i99999999999999999999"),
            Some(TypeCheck::Malformed(_))
        ));
        assert!(matches!(check("i00"), Some(TypeCheck::Malformed(_))));
        assert_eq!(check("index"), None);
    }

    fn float(e: i128, m: i128) -> Type {
        Type::app(FLOAT, vec![Attr::int(e), Attr::int(m)])
    }

    #[test]
    fn each_float_format_has_one_spelling() {
        for (name, e, m) in FLOAT_ALIASES {
            assert_eq!(float_type(e, m), Type::word(name));
            assert_eq!(core_type(&Type::word(name)), Some(CoreType::Float { e, m }));
            let generic = float(i128::from(e), i128::from(m));
            assert!(matches!(
                CoreTypes.check(&generic),
                Some(TypeCheck::Malformed(r)) if r.contains(name)
            ));
        }
        assert_eq!(float_type(5, 2), float(5, 2));
        assert_eq!(
            core_type(&float(5, 2)),
            Some(CoreType::Float { e: 5, m: 2 })
        );
        assert_eq!(CoreTypes.check(&float(4, 3)), Some(TypeCheck::Valid));
        assert_eq!(CoreTypes.check(&float(2, 1)), Some(TypeCheck::Valid));
    }

    #[test]
    fn float_formats_are_bounded_as_the_spec_says() {
        let check = |e, m| CoreTypes.check(&float(e, m));
        for (e, m) in [(1, 1), (2, 0), (0, 0), (0, 5)] {
            assert!(
                matches!(check(e, m), Some(TypeCheck::Invalid(_))),
                "{e} {m}"
            );
        }
        let widest = i128::from(MAX_WIDTH) - 3;
        assert_eq!(check(2, widest), Some(TypeCheck::Valid));
        for (e, m) in [(2, widest + 1), (-1, 3), (3, -1), (1 << 40, 1)] {
            assert!(
                matches!(check(e, m), Some(TypeCheck::Malformed(_))),
                "{e} {m}"
            );
        }
        assert_eq!(CoreTypes.check(&Type::app(FLOAT, vec![Attr::int(5)])), None);
        assert_eq!(CoreTypes.check(&Type::app("f32", vec![])), None);
        assert_eq!(CoreTypes.check(&Type::word("float")), None);
    }
}
