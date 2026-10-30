//! The core types (`lean/Fir/Core/Types.lean`, `Ty.decode` in
//! `lean/Fir/Core/Text.lean`, `Ty.Valid` in `lean/Fir/Core/Validation.lean`).
//!
//! `iN` is written `i` and `N` in decimal with no leading zeros. A width above
//! [`MAX_WIDTH`] does not decode (N3). `i0` decodes, and validation rejects
//! it. `ptr` is reserved: it decodes, and validation in M0 rejects every
//! value of type `ptr`.

use crate::Type;
use crate::registry::{TypeCheck, TypeSpec};

/// The widest integer type, `i16777215`: `2^24 - 1` bits, MLIR's limit.
pub const MAX_WIDTH: u32 = (1 << 24) - 1;

/// A core type, decoded.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CoreType {
    /// `iN`, a bitvector of `N` bits.
    Int(u32),
    /// The reserved type `ptr`.
    Ptr,
}

/// The type `iN` with `N = width`.
pub fn int_type(width: u32) -> Type {
    Type::word(format!("i{width}"))
}

/// The core type that `ty` writes, if it decodes as one.
pub fn core_type(ty: &Type) -> Option<CoreType> {
    decode(ty)?.ok()
}

/// The width of `ty` if it is `iN`.
pub fn int_width(ty: &Type) -> Option<u32> {
    match core_type(ty)? {
        CoreType::Int(w) => Some(w),
        CoreType::Ptr => None,
    }
}

/// `None` when `ty` is not a core type; an error when it looks like `iN` but
/// its width is not written as the spec requires.
fn decode(ty: &Type) -> Option<Result<CoreType, String>> {
    if ty.args.is_some() {
        return None;
    }
    if ty.name == "ptr" {
        return Some(Ok(CoreType::Ptr));
    }
    let digits = ty.name.strip_prefix('i')?;
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
}
