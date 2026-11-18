//! The second dialect in tree, `gpu`: a GPU kernel language
//! (ADR-2026-11-09-1545; `lean/Fir/Gpu/`).
//!
//! A host module holds a nested device module whose dialect set names
//! `gpu`, and the kernels are that module's functions. Each op asks the
//! work-item that runs it one question in one dimension of the grid, and
//! gives the answer as an `i32`:
//!
//! - `%i: i32 = gpu.work_item_id gpu.x`, its id within its work-group;
//! - `%g: i32 = gpu.work_group_id gpu.x`, its work-group's id;
//! - `%s: i32 = gpu.work_group_size gpu.x`, the size of a work-group;
//! - `%n: i32 = gpu.num_work_groups gpu.x`, the number of work-groups.
//!
//! The dimension, `gpu.x`, `gpu.y` or `gpu.z`, is the dialect's own
//! attribute. A question decodes from one dimension, no operand and one
//! integer result of any width; any other shape is a parse error, as
//! `Op.decode` in `lean/Fir/Gpu/Text.lean` says. Validation asks for an
//! `i32` (`Op.Valid` in `lean/Fir/Gpu/Validation.lean`). Every question is
//! pure (`lean/Fir/Gpu/Effects.lean`).
//!
//! `%p: ptr(3) = gpu.work_group_alloca i32 64` allocates in work-group
//! memory, any memory of the host's data layout (the human's ruling of
//! 2026-11-16 on #212): it is written, validated and declares its effects
//! as `alloca` does, without the kind, since its allocation lives for the
//! whole run of the kernel (`Gpu.allocRule` in
//! `lean/Fir/Gpu/Semantics.lean`). The dialect has no types of its own and
//! no lowering to core or native backend: it is terminal
//! (ADR-2026-11-09-1544).

use super::core::{
    self, allocation_effects, allocation_memory, check_work_group_shape, int_width,
    shape_attr_types, shape_decodes, type_list,
};
use crate::effects::Effects;
use crate::ir::{Attr, Type};
use crate::registry::{Dialect, OpContext, OpShape, OpSpec, OpTypes};

/// The dialect's name.
pub const NAME: &str = "gpu";

/// The dialect's questions, by name.
pub const QUERIES: [&str; 4] = [
    "gpu.work_item_id",
    "gpu.work_group_id",
    "gpu.work_group_size",
    "gpu.num_work_groups",
];

/// The op that allocates in work-group memory (`Gpu.allocName`).
pub const WORK_GROUP_ALLOCA: &str = "gpu.work_group_alloca";

/// The words of the three dimensions.
pub const DIMENSIONS: [&str; 3] = ["gpu.x", "gpu.y", "gpu.z"];

/// One op of the dialect, by its name.
struct Query(&'static str);

impl OpSpec for Query {
    fn name(&self) -> &str {
        self.0
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        let dimension = matches!(op.attrs, [Attr::Word(w)] if DIMENSIONS.contains(&w.as_str()));
        if !dimension {
            return Err(format!(
                "{} takes one dimension, gpu.x, gpu.y or gpu.z",
                self.0
            ));
        }
        if op.operands.is_empty() && matches!(op.results, [r] if int_width(r).is_some()) {
            return Ok(OpShape::default());
        }
        Err(format!("{} takes no operand and gives one integer", self.0))
    }

    fn check(&self, _cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        if matches!(op.results, [r] if int_width(r) == Some(32)) {
            Ok(())
        } else {
            Err(format!("{} gives an i32", self.0))
        }
    }

    /// Pure (`Gpu.Effects`): an id or a size is fixed for the whole run of
    /// a work-item.
    fn effects(&self, _op: &OpTypes<'_>) -> Effects {
        Effects::PURE
    }
}

/// `%p: ptr(3) = gpu.work_group_alloca i32 4 align(4)`.
struct WorkGroupAlloca;

impl OpSpec for WorkGroupAlloca {
    fn name(&self) -> &str {
        WORK_GROUP_ALLOCA
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if allocation_memory(op).is_none() {
            return Err(format!(
                "{WORK_GROUP_ALLOCA} takes no operands and defines a pointer, not {} -> {}",
                type_list(op.operands),
                type_list(op.results)
            ));
        }
        if !shape_decodes(op.attrs) {
            return Err(format!(
                "{WORK_GROUP_ALLOCA} takes a type, a count that is not negative and not 1, \
                 and align(A), in that order, the last two when given"
            ));
        }
        Ok(OpShape::default())
    }

    fn check(&self, _cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        check_work_group_shape(WORK_GROUP_ALLOCA, op.attrs)
    }

    /// The type it allocates values of, when that is a valid pointer type
    /// (`Gpu.Op.attrTypes`).
    fn attr_types(&self, attrs: &[Attr]) -> Vec<Type> {
        shape_attr_types(attrs)
    }

    /// Allocates in its memory (`Gpu.Op.effects`).
    fn effects(&self, op: &OpTypes<'_>) -> Effects {
        allocation_effects(op)
    }
}

/// The dialect, ready to register beside the core.
pub fn dialect() -> Dialect {
    QUERIES
        .into_iter()
        .fold(Dialect::new(NAME).depends_on(core::NAME), |d, name| {
            d.op(Query(name))
        })
        .op(WorkGroupAlloca)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialects::core::{int_type, ptr_type};
    use crate::effects::MemSet;

    fn decode(attrs: &[Attr], operands: &[Type], results: &[Type]) -> Result<OpShape, String> {
        Query("gpu.work_item_id").decode(&OpTypes {
            attrs,
            operands,
            results,
        })
    }

    #[test]
    fn each_dimension_decodes_at_any_integer_width() {
        for d in DIMENSIONS {
            for w in [1, 32, 64] {
                assert_eq!(
                    decode(&[Attr::word(d)], &[], &[int_type(w)]),
                    Ok(OpShape::default())
                );
            }
        }
    }

    #[test]
    fn every_other_shape_does_not_decode() {
        let i32 = int_type(32);
        let x = Attr::word("gpu.x");
        for (attrs, operands, results) in [
            (vec![], vec![], vec![i32.clone()]),
            (vec![Attr::word("gpu.w")], vec![], vec![i32.clone()]),
            (vec![Attr::word("x")], vec![], vec![i32.clone()]),
            (vec![x.clone(), x.clone()], vec![], vec![i32.clone()]),
            (vec![x.clone()], vec![i32.clone()], vec![i32.clone()]),
            (vec![x.clone()], vec![], vec![]),
            (vec![x.clone()], vec![], vec![ptr_type(0)]),
            (vec![x.clone()], vec![], vec![i32.clone(), i32.clone()]),
        ] {
            assert!(decode(&attrs, &operands, &results).is_err(), "{attrs:?}");
        }
    }

    fn alloc(attrs: &[Attr], operands: &[Type], results: &[Type]) -> Result<(), String> {
        let op = OpTypes {
            attrs,
            operands,
            results,
        };
        let symbols = crate::SymbolTable::of(&[]);
        let cx = OpContext {
            symbols: &symbols,
            func: "k",
            results: &[],
        };
        WorkGroupAlloca.decode(&op)?;
        WorkGroupAlloca.check(&cx, &op)
    }

    #[test]
    fn a_work_group_allocation_is_written_as_alloca_without_its_kind() {
        let p3 = [ptr_type(3)];
        let align = |a| Attr::App("align".into(), vec![Attr::int(a)]);
        let float_attr = |e, m| Attr::App("float".into(), vec![Attr::int(e), Attr::int(m)]);
        for attrs in [
            vec![Attr::word("i32")],
            vec![Attr::word("i32"), Attr::int(64)],
            vec![Attr::word("ptr"), align(8)],
            vec![Attr::word("f32"), Attr::int(64)],
            vec![Attr::word("f16"), align(2)],
            vec![float_attr(2, 1)],
        ] {
            assert_eq!(alloc(&attrs, &[], &p3), Ok(()), "{attrs:?}");
        }
        for (attrs, operands, results) in [
            (
                vec![Attr::word("global"), Attr::word("i32")],
                vec![],
                p3.to_vec(),
            ),
            (vec![Attr::word("i32"), Attr::int(1)], vec![], p3.to_vec()),
            (vec![], vec![], p3.to_vec()),
            (vec![Attr::word("i32")], vec![int_type(32)], p3.to_vec()),
            (vec![Attr::word("i32")], vec![], vec![int_type(32)]),
            (vec![Attr::word("i32"), Attr::int(0)], vec![], p3.to_vec()),
            (vec![Attr::word("i32"), align(3)], vec![], p3.to_vec()),
        ] {
            assert!(alloc(&attrs, &operands, &results).is_err(), "{attrs:?}");
        }
        assert_eq!(
            alloc(&[float_attr(1, 1)], &[], &p3),
            Err("gpu.work_group_alloca allocates a valid float type, not float(1, 1)".into())
        );
    }

    #[test]
    fn a_work_group_allocation_allocates_in_its_memory() {
        let attrs = [Attr::App("ptr".into(), vec![Attr::int(5)])];
        let results = [ptr_type(3)];
        let op = OpTypes {
            attrs: &attrs,
            operands: &[],
            results: &results,
        };
        assert_eq!(
            WorkGroupAlloca.effects(&op).allocates,
            MemSet::These(vec!["3".into()])
        );
        assert_eq!(WorkGroupAlloca.attr_types(&attrs), vec![ptr_type(5)]);
    }

    #[test]
    fn the_dialect_registers_beside_the_core() {
        crate::dialects::in_tree();
    }
}
