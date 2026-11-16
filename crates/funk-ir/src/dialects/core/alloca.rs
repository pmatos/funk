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
//! alignment that is a power of two no larger than [`MemLayout::LIMIT`], as
//! the data layout's own alignments are, and a valid integer or pointer
//! type; a pointer type names a memory that the data layout must declare
//! ([`OpSpec::attr_types`]). A float type has no encoding in units. The count
//! has no bound: an allocation larger than a machine holds is a resource
//! error at run time. The op is never UB and never gives poison: it
//! allocates in its memory, and the frame of its call frees the allocation
//! when the call returns.
//!
//! [`MemLayout::LIMIT`]: crate::ir::MemLayout::LIMIT
//! [`OpSpec::attr_types`]: crate::registry::OpSpec::attr_types

use super::align::{check_align, decode_align};
use super::types::{CoreType, FLOAT_ALIASES, MAX_MEMORY, MAX_WIDTH, alias, core_type, ptr_type};
use crate::effects::{Effects, MemSet};
use crate::ir::MemLayout;
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};
use crate::{Attr, Int, Type};

/// The kinds of an allocation, as words (`AllocKind.word`).
const ALLOC_KINDS: [&str; 3] = ["stack", "global", "heap"];

/// The type `alloca` carries, read with no bound (`Ty.decodeAny`): `iN`
/// with its digits, a float format, or a pointer of a memory, with the
/// memory's digits.
#[derive(Clone, Debug, PartialEq, Eq)]
enum AnyType {
    Int(Int),
    Float,
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

/// Reads a core type as the spec writes it, with no bound on a width or a
/// memory, or `None` when the attribute is not one.
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
            [Attr::Int(n)] if nonneg(n) && n.as_str() != "0" => Some(AnyType::Ptr(n.clone())),
            _ => None,
        },
        _ => None,
    }
}

/// The attributes of an allocation after its kind: its type, its count and
/// its alignment. `gpu.work_group_alloca` writes them as `alloca` does,
/// with no kind (`decodeAlloc` in `lean/Fir/Gpu/Text.lean`).
struct Shape<'a> {
    ty: AnyType,
    count: Option<&'a Int>,
    align: Option<&'a Int>,
}

/// The parts of a decoded `alloca`: its kind, and the shape that follows.
struct Parts<'a> {
    kind: &'a str,
    shape: Shape<'a>,
}

/// Reads the attributes of an allocation after its kind, or `None` when
/// they do not decode.
fn shape(attrs: &[Attr]) -> Option<Shape<'_>> {
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

/// Reads the attributes of `alloca`, or `None` when they do not decode.
fn parts(attrs: &[Attr]) -> Option<Parts<'_>> {
    let [Attr::Word(kind), rest @ ..] = attrs else {
        return None;
    };
    if !ALLOC_KINDS.contains(&kind.as_str()) {
        return None;
    }
    Some(Parts {
        kind,
        shape: shape(rest)?,
    })
}

/// Whether the attributes of an allocation after its kind decode.
pub(crate) fn shape_decodes(attrs: &[Attr]) -> bool {
    shape(attrs).is_some()
}

/// The rules of an allocation beyond its kind, for the op `op` whose
/// attributes after its kind are `attrs`: at least one value, an alignment
/// that `check_align` accepts, and a valid integer or pointer type
/// (`Core.Op.Valid`, `Gpu.Op.Valid`). Attributes that do not decode break
/// no rule here: decoding reports them.
pub(crate) fn check_shape(op: &str, attrs: &[Attr]) -> Result<(), String> {
    let Some(p) = shape(attrs) else {
        return Ok(());
    };
    if p.count.is_some_and(|c| c.as_str() == "0") {
        return Err(format!("{op} allocates at least one value, not 0"));
    }
    if let Some(a) = p.align {
        check_align(op, a.as_str())?;
    }
    let valid_width = |w: &Int| {
        w.as_str()
            .parse::<u32>()
            .is_ok_and(|w| (1..=MAX_WIDTH).contains(&w))
    };
    match &p.ty {
        AnyType::Int(w) if valid_width(w) => Ok(()),
        AnyType::Int(w) => Err(format!(
            "{op} allocates a valid integer type, not i{}",
            w.as_str()
        )),
        AnyType::Ptr(n) if valid_memory(n).is_some() => Ok(()),
        AnyType::Ptr(n) => Err(format!(
            "{op} allocates a valid pointer type, not ptr({})",
            n.as_str()
        )),
        AnyType::Float => Err(format!(
            "{op} allocates an integer or a pointer type in M1, not a float: \
             a float has no encoding in units"
        )),
    }
}

/// The type that an allocation whose attributes after its kind are
/// `attrs` allocates values of, when that is a valid pointer type, whose
/// memory the data layout must declare (`Core.Op.attrTypes`,
/// `Gpu.Op.attrTypes`). An integer type names no memory, and a type that
/// is not valid breaks the op's own rule.
pub(crate) fn shape_attr_types(attrs: &[Attr]) -> Vec<Type> {
    match shape(attrs).map(|p| p.ty) {
        Some(AnyType::Ptr(n)) => valid_memory(&n).map(ptr_type).into_iter().collect(),
        _ => Vec::new(),
    }
}

/// What a valid `alloca` allocates, read from its attributes: the type of
/// its values, an integer or a pointer type; its count, written when it is
/// not 1; and its alignment, written when the op gives one. A backend sizes
/// the allocation from them with its memory's layout entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Allocation<'a> {
    /// The type of the values it has room for: `Int` or `Ptr`.
    pub element: CoreType,
    /// The count of values, when it is not 1.
    pub count: Option<&'a Int>,
    /// The alignment it writes, in units, when it writes one.
    pub align: Option<u32>,
}

/// The allocation of an `alloca` with the attributes `attrs`, or `None`
/// unless they decode with the kind `stack`, the one M1 has, and an
/// element and an alignment that validation accepts.
pub fn allocation(attrs: &[Attr]) -> Option<Allocation<'_>> {
    let p = parts(attrs).filter(|p| p.kind == "stack")?.shape;
    let element = match &p.ty {
        AnyType::Int(w) => CoreType::Int(
            w.as_str()
                .parse::<u32>()
                .ok()
                .filter(|w| (1..=MAX_WIDTH).contains(w))?,
        ),
        AnyType::Ptr(n) => CoreType::Ptr(valid_memory(n)?),
        AnyType::Float => return None,
    };
    let align = match p.align {
        Some(a) => Some(
            a.as_str()
                .parse::<u32>()
                .ok()
                .filter(|&a| MemLayout::valid_align(a))?,
        ),
        None => None,
    };
    Some(Allocation {
        element,
        count: p.count,
        align,
    })
}

/// The memory of the pointer that an allocation defines, when it has no
/// operands and one pointer result.
pub(crate) fn memory(op: &OpTypes<'_>) -> Option<u32> {
    match (op.operands, op.results) {
        ([], [r]) => match core_type(r)? {
            CoreType::Ptr(n) => Some(n),
            CoreType::Int(_) | CoreType::Float { .. } => None,
        },
        _ => None,
    }
}

/// The effects of an allocation: it allocates in the memory of its result
/// (`Core.Op.effects`, `Gpu.Op.effects`).
pub(crate) fn allocation_effects(op: &OpTypes<'_>) -> Effects {
    Effects {
        allocates: memory(op).map_or(MemSet::NONE, |n| MemSet::These(vec![n.to_string()])),
        ..Effects::PURE
    }
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
        check_shape("alloca", &op.attrs[1..])
    }

    /// The type it allocates values of, when that is a valid pointer type,
    /// whose memory the data layout must declare (`Core.Op.attrTypes`). An
    /// integer type names no memory, and a type that is not valid breaks
    /// the op's own rule.
    fn attr_types(&self, attrs: &[Attr]) -> Vec<Type> {
        match parts(attrs) {
            Some(_) => shape_attr_types(&attrs[1..]),
            None => Vec::new(),
        }
    }

    /// Allocates in its memory (`Core.Op.effects`).
    fn effects(&self, op: &OpTypes<'_>) -> Effects {
        allocation_effects(op)
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

    fn ptr_attr(n: i128) -> Attr {
        Attr::App("ptr".into(), vec![Attr::int(n)])
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
    fn a_valid_allocation_gives_its_element_count_and_alignment() {
        let attrs = [word("stack"), word("i32"), Attr::int(4), align(8)];
        let a = allocation(&attrs).unwrap();
        assert_eq!(a.element, CoreType::Int(32));
        assert_eq!(a.count.map(Int::as_str), Some("4"));
        assert_eq!(a.align, Some(8));
        let attrs = [word("stack"), ptr_attr(1)];
        let p = allocation(&attrs).unwrap();
        assert_eq!(
            (p.element, p.count, p.align),
            (CoreType::Ptr(1), None, None)
        );
        let attrs = [word("stack"), word("ptr")];
        assert_eq!(allocation(&attrs).unwrap().element, CoreType::Ptr(0));
        for bad in [
            vec![word("stack"), word("f32")],
            vec![word("stack"), word("i0")],
            vec![word("stack")],
            vec![word("heap"), word("i32")],
            vec![word("stack"), word("i32"), align(3)],
        ] {
            assert_eq!(allocation(&bad), None, "{bad:?}");
        }
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
            vec![word("stack"), word("i32"), align(1 << 24)],
            vec![word("stack"), word("i0")],
            vec![word("stack"), word("i16777216")],
            vec![word("stack"), word("f32")],
            vec![
                word("stack"),
                Attr::App("float".into(), vec![Attr::int(8), Attr::int(7)]),
            ],
            vec![word("stack"), ptr_attr(1 << 24)],
        ] {
            assert!(check(&attrs).is_err(), "{attrs:?}");
        }
        let f = float_type(5, 10);
        assert_eq!(f.name, "f16");
        for attrs in [
            vec![word("stack"), word("i32"), Attr::int(1 << 40)],
            vec![word("stack"), word("i32"), Attr::int(1 << 100)],
            vec![word("stack"), word("i32"), align(1 << 23)],
            vec![word("stack"), word("i16777215"), align(1)],
            vec![word("stack"), word("ptr")],
            vec![word("stack"), ptr_attr(1), Attr::int(3), align(2)],
            vec![word("stack"), ptr_attr(i128::from(MAX_MEMORY))],
        ] {
            assert_eq!(check(&attrs), Ok(()), "{attrs:?}");
        }
    }

    #[test]
    fn alignments_are_powers_of_two_up_to_the_layouts_limit() {
        for a in ["1", "2", "1024", "8388608"] {
            assert_eq!(check_align("alloca", a), Ok(()), "{a}");
        }
        let not_power = |a: &str| format!("alloca aligns to a power of two of units, not {a}");
        let above = |a: &str| {
            format!("alloca aligns to at most 16777215 units, as the data layout does, not {a}")
        };
        for a in ["0", "3", "12", "16777215"] {
            assert_eq!(check_align("alloca", a), Err(not_power(a)), "{a}");
        }
        for a in ["16777216", "4294967296", "1180591620717411303424"] {
            assert_eq!(check_align("alloca", a), Err(above(a)), "{a}");
        }
    }

    #[test]
    fn a_pointer_element_names_its_memory() {
        assert_eq!(
            Alloca.attr_types(&[word("stack"), word("ptr"), Attr::int(2)]),
            vec![ptr_type(0)]
        );
        assert_eq!(
            Alloca.attr_types(&[word("stack"), ptr_attr(5), align(8)]),
            vec![ptr_type(5)]
        );
        for attrs in [
            vec![word("stack"), word("i32")],
            vec![word("stack"), word("f32")],
            vec![word("stack"), ptr_attr(1 << 24)],
            vec![word("stack")],
        ] {
            assert_eq!(Alloca.attr_types(&attrs), vec![], "{attrs:?}");
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
