//! Stack allocation: `alloca` (`decodeAlloca` in
//! `lean/Fir/Core/AllocaText.lean`, `allocaRule` in
//! `lean/Fir/Core/Alloca.lean`, its rule in `Op.Valid` in
//! `lean/Fir/Core/Validation.lean`; ADR-2026-11-14-0915).
//!
//! `%p: ptr<N> = alloca KIND TYPE [COUNT] [align(A)]` allocates room for
//! `COUNT` values of `TYPE` in memory `N`, the memory of its result, and
//! defines the pointer to the allocation. It has no operands. Its attributes
//! are, in order: the kind, `stack`, `global` or `heap`; the type, written as
//! a type is and read with no bound on its width or memory; the count, an
//! integer that is not negative and not 1, written only when it is not 1;
//! and `align(A)`, with `A` not negative, written only when the op gives an
//! alignment. Any other shape does not decode.
//!
//! Validation accepts only the kind `stack`, a count of at least 1, an
//! alignment that is a power of two, and a valid integer type. The op is never UB and never gives
//! poison: it allocates in its memory, and the frame of its call frees the
//! allocation when the call returns.

use super::types::{CoreType, FLOAT_ALIASES, MAX_WIDTH, alias, core_type};
use crate::effects::{Effects, MemSet};
use crate::ir::Nat;
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};
use crate::{Attr, Int};

/// The kinds of an allocation, as words (`AllocKind.word`).
const ALLOC_KINDS: [&str; 3] = ["stack", "global", "heap"];

/// The type `alloca` carries, read with no bound (`Ty.decodeAny`): `iN`
/// with its digits, a float format, or a pointer of a memory.
#[derive(Clone, Debug, PartialEq, Eq)]
enum AnyType {
    Int(Int),
    Float,
    Ptr,
}

/// An integer not negative, from its canonical spelling.
fn nonneg(i: &Int) -> bool {
    !i.is_negative()
}

/// Reads a core type as the spec writes it, with no bound on a width or a
/// memory, or `None` when the attribute is not one.
fn decode_any(a: &Attr) -> Option<AnyType> {
    match a {
        Attr::Word(w) if w == "ptr" => Some(AnyType::Ptr),
        Attr::Word(w) => match w.strip_prefix('i') {
            Some(digits) => {
                let i = Int::parse(digits)?;
                nonneg(&i).then_some(AnyType::Int(i))
            }
            None => FLOAT_ALIASES
                .iter()
                .any(|f| f.0 == w)
                .then_some(AnyType::Float),
        },
        Attr::App(h, args) if h == "float" => match args.as_slice() {
            [Attr::Int(e), Attr::Int(m)] if nonneg(e) && nonneg(m) => {
                let format = e.as_str().parse().ok().zip(m.as_str().parse().ok());
                format
                    .and_then(|(e, m)| alias(e, m))
                    .is_none()
                    .then_some(AnyType::Float)
            }
            _ => None,
        },
        Attr::App(h, args) if h == "ptr" => match args.as_slice() {
            [Attr::Int(n)] if nonneg(n) && n.as_str() != "0" => Some(AnyType::Ptr),
            _ => None,
        },
        _ => None,
    }
}

/// The parts of a decoded `alloca`: its kind, its type, its count and its
/// alignment.
struct Parts<'a> {
    kind: &'a str,
    ty: AnyType,
    count: Option<&'a Int>,
    align: Option<&'a Int>,
}

/// Reads the attributes of `alloca`, or `None` when they do not decode.
fn parts(attrs: &[Attr]) -> Option<Parts<'_>> {
    let [Attr::Word(kind), ty, rest @ ..] = attrs else {
        return None;
    };
    if !ALLOC_KINDS.contains(&kind.as_str()) {
        return None;
    }
    let ty = decode_any(ty)?;
    let (count, rest) = match rest {
        [Attr::Int(c), rest @ ..] if nonneg(c) && c.as_str() != "1" => (Some(c), rest),
        [Attr::Int(_), ..] => return None,
        rest => (None, rest),
    };
    let align = match rest {
        [] => None,
        [Attr::App(h, args)] if h == "align" => match args.as_slice() {
            [Attr::Int(a)] if nonneg(a) => Some(a),
            _ => return None,
        },
        _ => return None,
    };
    Some(Parts {
        kind,
        ty,
        count,
        align,
    })
}

/// The memory of the pointer `alloca` defines, when it has no operands and
/// one pointer result.
fn memory(op: &OpTypes<'_>) -> Option<u32> {
    match (op.operands, op.results) {
        ([], [r]) => match core_type(r)? {
            CoreType::Ptr(n) => Some(n),
            CoreType::Int(_) | CoreType::Float { .. } => None,
        },
        _ => None,
    }
}

/// Whether the decimal digits `s`, with no sign, spell a power of two, of
/// any size (`isPowerOfTwo`).
fn power_of_two(s: &str) -> bool {
    Nat::from_decimal(s).is_power_of_two()
}

/// `%p: ptr = alloca stack i32 4 align(4)`.
pub(super) struct Alloca;

impl OpSpec for Alloca {
    fn name(&self) -> &str {
        "alloca"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if memory(op).is_none() {
            return Err(format!(
                "alloca takes no operands and defines a pointer, not {} -> {}",
                super::type_list(op.operands),
                super::type_list(op.results)
            ));
        }
        if parts(op.attrs).is_none() {
            return Err(
                "alloca takes a kind, a type, a count that is not negative and not 1, \
                        and align(A), in that order, the last two when given"
                    .into(),
            );
        }
        Ok(OpShape::default())
    }

    fn check(&self, _cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        let Some(p) = parts(op.attrs) else {
            return Ok(());
        };
        if p.kind != "stack" {
            return Err(format!(
                "alloca allocates on the stack in M1, not as {}: global and heap are hooks",
                p.kind
            ));
        }
        if p.count.is_some_and(|c| c.as_str() == "0") {
            return Err("alloca allocates at least one value, not 0".into());
        }
        if let Some(a) = p.align
            && !power_of_two(a.as_str())
        {
            return Err(format!(
                "alloca aligns to a power of two of units, not {}",
                a.as_str()
            ));
        }
        let valid_width = |w: &Int| {
            w.as_str()
                .parse::<u32>()
                .is_ok_and(|w| (1..=MAX_WIDTH).contains(&w))
        };
        match &p.ty {
            AnyType::Int(w) if valid_width(w) => Ok(()),
            AnyType::Int(w) => Err(format!(
                "alloca allocates a valid integer type, not i{}",
                w.as_str()
            )),
            AnyType::Float | AnyType::Ptr => {
                Err("alloca allocates an integer type in M1, not a float or a pointer".into())
            }
        }
    }

    /// Allocates in its memory (`Core.Op.effects`).
    fn effects(&self, op: &OpTypes<'_>) -> Effects {
        Effects {
            allocates: memory(op).map_or(MemSet::NONE, |n| MemSet::These(vec![n.to_string()])),
            ..Effects::PURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialects::core::{float_type, int_type, ptr_type};
    use crate::{SymbolTable, Type};

    fn types<'a>(attrs: &'a [Attr], results: &'a [Type]) -> OpTypes<'a> {
        OpTypes {
            attrs,
            operands: &[],
            results,
        }
    }

    fn word(w: &str) -> Attr {
        Attr::word(w)
    }

    fn align(a: i128) -> Attr {
        Attr::App("align".into(), vec![Attr::int(a)])
    }

    fn check(attrs: &[Attr]) -> Result<(), String> {
        let symbols = SymbolTable::of(&[]);
        let cx = OpContext {
            symbols: &symbols,
            func: "f",
            results: &[],
        };
        let results = [ptr_type(0)];
        let op = types(attrs, &results);
        Alloca.decode(&op)?;
        Alloca.check(&cx, &op)
    }

    #[test]
    fn the_rulings_examples_decode_and_validate() {
        for (attrs, n) in [
            (vec![word("stack"), word("i32")], 0),
            (vec![word("stack"), word("i32"), Attr::int(4)], 0),
            (vec![word("stack"), word("i8"), Attr::int(12), align(4)], 1),
            (vec![word("stack"), word("i64"), align(1)], 7),
        ] {
            let results = [ptr_type(n)];
            assert_eq!(
                Alloca.decode(&types(&attrs, &results)),
                Ok(OpShape::default())
            );
        }
        assert_eq!(
            check(&[word("stack"), word("i8"), Attr::int(12), align(4)]),
            Ok(())
        );
    }

    #[test]
    fn other_shapes_do_not_decode() {
        let i32 = int_type(32);
        let p = ptr_type(0);
        let ok = [word("stack"), word("i32")];
        for (attrs, operands, results) in [
            (ok.to_vec(), vec![], vec![i32.clone()]),
            (ok.to_vec(), vec![i32.clone()], vec![p.clone()]),
            (ok.to_vec(), vec![], vec![p.clone(), p.clone()]),
            (vec![word("frame"), word("i32")], vec![], vec![p.clone()]),
            (vec![word("stack")], vec![], vec![p.clone()]),
            (
                vec![word("stack"), word("i32"), Attr::int(1)],
                vec![],
                vec![p.clone()],
            ),
            (
                vec![word("stack"), word("i32"), Attr::int(-2)],
                vec![],
                vec![p.clone()],
            ),
            (vec![word("stack"), word("i032")], vec![], vec![p.clone()]),
            (
                vec![word("stack"), word("i32"), align(-4)],
                vec![],
                vec![p.clone()],
            ),
            (
                vec![word("stack"), word("i32"), align(4), Attr::int(2)],
                vec![],
                vec![p.clone()],
            ),
            (vec![word("stack"), Attr::int(4)], vec![], vec![p.clone()]),
        ] {
            let op = OpTypes {
                attrs: &attrs,
                operands: &operands,
                results: &results,
            };
            assert!(Alloca.decode(&op).is_err(), "{attrs:?}");
        }
    }

    #[test]
    fn validation_rejects_what_m1_does_not_allow() {
        for attrs in [
            vec![word("heap"), word("i32")],
            vec![word("global"), word("i32")],
            vec![word("stack"), word("i32"), Attr::int(0)],
            vec![word("stack"), word("i32"), align(3)],
            vec![word("stack"), word("i32"), align(0)],
            vec![word("stack"), word("i32"), align((1 << 64) + 2)],
            vec![word("stack"), word("i0")],
            vec![word("stack"), word("i16777216")],
            vec![word("stack"), word("f32")],
            vec![word("stack"), word("ptr")],
        ] {
            assert!(check(&attrs).is_err(), "{attrs:?}");
        }
        let f = float_type(5, 10);
        assert_eq!(f.name, "f16");
        for attrs in [
            vec![word("stack"), word("i32"), Attr::int(1 << 40)],
            vec![word("stack"), word("i32"), align(1 << 70)],
            vec![word("stack"), word("i16777215"), align(1)],
        ] {
            assert_eq!(check(&attrs), Ok(()), "{attrs:?}");
        }
    }

    #[test]
    fn powers_of_two_of_any_size() {
        for s in ["1", "2", "4", "1024", "1180591620717411303424"] {
            assert!(power_of_two(s), "{s}");
        }
        for s in ["0", "3", "6", "12", "1180591620717411303423"] {
            assert!(!power_of_two(s), "{s}");
        }
    }

    #[test]
    fn alloca_allocates_in_its_memory() {
        for n in [0, 1, 7] {
            let (attrs, results) = ([word("stack"), word("i32")], [ptr_type(n)]);
            let effects = Alloca.effects(&types(&attrs, &results));
            assert_eq!(
                effects,
                Effects {
                    allocates: MemSet::These(vec![n.to_string()]),
                    ..Effects::PURE
                }
            );
        }
    }
}
