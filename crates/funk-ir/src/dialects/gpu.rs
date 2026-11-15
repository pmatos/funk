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
//! attribute. An op decodes from one dimension, no operand and one integer
//! result of any width; any other shape is a parse error, as `Op.decode`
//! in `lean/Fir/Gpu/Text.lean` says. Validation asks for an `i32`
//! (`Op.Valid` in `lean/Fir/Gpu/Validation.lean`). Every op is pure
//! (`lean/Fir/Gpu/Effects.lean`). The dialect has no types of its own and
//! no lowering to core or native backend: it is terminal
//! (ADR-2026-11-09-1544).

use super::core::{self, int_type, int_width};
use crate::effects::Effects;
use crate::ir::Attr;
use crate::registry::{Dialect, OpContext, OpShape, OpSpec, OpTypes};

/// The dialect's name.
pub const NAME: &str = "gpu";

/// The dialect's ops, by name.
pub const OPS: [&str; 4] = [
    "gpu.work_item_id",
    "gpu.work_group_id",
    "gpu.work_group_size",
    "gpu.num_work_groups",
];

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
        if op.results == [int_type(32)] {
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

/// The dialect, ready to register beside the core.
pub fn dialect() -> Dialect {
    OPS.into_iter()
        .fold(Dialect::new(NAME).depends_on(core::NAME), |d, name| {
            d.op(Query(name))
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Type;
    use crate::dialects::core::ptr_type;

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

    #[test]
    fn the_dialect_registers_beside_the_core() {
        let mut r = crate::Registry::core();
        r.register(dialect()).expect("gpu registers");
    }
}
