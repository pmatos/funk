//! Control flow: `br`, `cond_br` and `ret` (`lean/Fir/Core/Ops.lean`,
//! `Op.decode` in `lean/Fir/Core/Text.lean`, `Op.Valid` in
//! `lean/Fir/Core/Validation.lean`).
//!
//! These are the terminators. `br` jumps to its one successor and
//! `cond_br` to the first of its two when its `i1` condition is `true`, the
//! second when it is `false`; each passes the values its successor names
//! to that block's arguments. Neither takes attributes or defines values,
//! and `br` takes no operands: the values it passes belong to its
//! successor, which validation checks against the block it names
//! (`Func.SuccValid`), with the dominance of every value it passes. A
//! successor that names no block, or passes a value the function does not
//! define, still decodes (ADR-2026-10-30-0815).
//!
//! `ret` returns its operands: any number of values of core types, none
//! included (ADR-2026-10-30-0816). It returns the function's result types,
//! which validation checks.

use super::type_list;
use super::types::{CoreType, core_type};
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};

/// A terminator with `successors` successors.
fn terminator(successors: usize) -> OpShape {
    OpShape {
        terminator: true,
        successors,
        ..OpShape::default()
    }
}

/// Checks that the branch `name` has no attributes and defines no values.
fn bare(name: &str, op: &OpTypes<'_>) -> Result<(), String> {
    if !op.attrs.is_empty() {
        return Err(format!("{name} takes no attributes"));
    }
    if !op.results.is_empty() {
        return Err(format!("{name} defines no values"));
    }
    Ok(())
}

/// `br ^b(%x, %y)`.
pub(super) struct Br;

impl OpSpec for Br {
    fn name(&self) -> &str {
        "br"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        bare("br", op)?;
        if !op.operands.is_empty() {
            return Err(format!(
                "br takes no operands, not {}: the values it passes belong to its successor",
                type_list(op.operands)
            ));
        }
        Ok(terminator(1))
    }
}

/// `cond_br %c, ^then(%x), ^else(%y)`.
pub(super) struct CondBr;

impl OpSpec for CondBr {
    fn name(&self) -> &str {
        "cond_br"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        bare("cond_br", op)?;
        match op.operands {
            [c] if core_type(c) == Some(CoreType::Int(1)) => Ok(terminator(2)),
            _ => Err(format!(
                "cond_br takes one operand, its i1 condition, not {}",
                type_list(op.operands)
            )),
        }
    }
}

/// `ret %a, %b`.
pub(super) struct Ret;

impl OpSpec for Ret {
    fn name(&self) -> &str {
        "ret"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if !op.attrs.is_empty() {
            return Err("ret takes no attributes".into());
        }
        if !op.results.is_empty() {
            return Err("ret defines no values".into());
        }
        if let Some(t) = op.operands.iter().find(|t| core_type(t).is_none()) {
            return Err(format!("ret returns values of core types, not {t}"));
        }
        Ok(terminator(0))
    }

    fn check(&self, cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        if op.operands == cx.results {
            return Ok(());
        }
        Err(format!(
            "ret returns {} but the function returns {}",
            type_list(op.operands),
            type_list(cx.results)
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialects::core::int_type;
    use crate::{Attr, Type};

    fn decode(spec: &dyn OpSpec, attrs: &[Attr], operands: &[Type], results: &[Type]) -> String {
        match spec.decode(&OpTypes {
            attrs,
            operands,
            results,
        }) {
            Ok(shape) => format!("{} successors", shape.successors),
            Err(why) => why,
        }
    }

    #[test]
    fn branches_decode_as_the_spec_reads_them() {
        let (i1, i8) = (int_type(1), int_type(8));
        let ptr = Type::word("ptr");
        let one = std::slice::from_ref(&i1);
        assert_eq!(decode(&Br, &[], &[], &[]), "1 successors");
        assert_eq!(decode(&CondBr, &[], one, &[]), "2 successors");
        for (spec, operands) in [(&Br as &dyn OpSpec, &[][..]), (&CondBr, one)] {
            let name = spec.name();
            let words = decode(spec, &[Attr::word("nsw")], operands, &[]);
            assert_eq!(words, format!("{name} takes no attributes"));
            let result = decode(spec, &[], operands, one);
            assert_eq!(result, format!("{name} defines no values"));
        }
        assert!(decode(&Br, &[], one, &[]).starts_with("br takes no operands"));
        for operands in [vec![], vec![i8], vec![ptr], vec![i1.clone(), i1]] {
            let why = decode(&CondBr, &[], &operands, &[]);
            assert!(why.starts_with("cond_br takes one operand"), "{why}");
        }
    }
}
