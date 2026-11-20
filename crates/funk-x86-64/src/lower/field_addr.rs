//! The field address `fieldaddr` (`dialects/core/field_addr.rs` in
//! `funk-ir`; `docs/decisions/x86-64-backend-lowering-memory.md#field-addresses`).
//!
//! `fieldaddr @s i %p` adds the offset of the field `i` of the layout `@s`
//! to the address, and `fieldaddr @s i %p, %k` adds `k` times the field's
//! stride too: the units of one value of its type rounded up to its
//! alignment, as `Field.place` in `lean/Fir/Execution/RunItems.lean` gives
//! it. The layout is the first of the module's own table with that symbol,
//! the one validation checked the op against. Its memory is the pointer's,
//! which the backend realises with 8-bit units, or the pointer is already
//! reported where it is defined, so the units are bytes.
//!
//! The index is read as signed, as `ptradd`'s offset is, and an `i128`
//! index takes its low half. The address wraps at 64 bits where the spec's
//! offset does not; the two agree on every access the spec allows. The
//! field's type is not a value of the op, so a field of a type that the
//! backend does not lower, such as `i24`, still has its address computed.

use std::collections::HashMap;

use funk_ir::ir::layout;
use funk_ir::text::print_symbol;
use funk_ir::{Attr, Field, Item, MemLayout, Module, Op, Registry};

use super::{Cx, Lower, Unlowered, memory};
use crate::asm::Reg;

pub(super) fn lowering(name: &str) -> Option<Lower> {
    (name == "fieldaddr").then_some(field_addr as Lower)
}

/// The fields of each layout of a module's own table, by its symbol: each
/// field's offset and stride in bytes, or `None` when its type may not be a
/// field, which validation rejects.
pub struct Places<'m>(HashMap<&'m str, Vec<Option<(u64, i32)>>>);

impl<'m> Places<'m> {
    /// The places of `m`'s layouts, the first with each symbol, as
    /// `SymbolTable::layout` finds it. A module with no layout builds no
    /// registry.
    pub fn of(m: &'m Module) -> Places<'m> {
        let mut places = HashMap::new();
        let mut core = None;
        let entry = |n: u64| {
            u32::try_from(n)
                .ok()
                .and_then(|n| layout::memory(&m.layout, n))
                .unwrap_or(MemLayout::DEFAULT)
        };
        for a in m.items.iter().filter_map(Item::as_aggregate) {
            if places.contains_key(a.name.as_str()) {
                continue;
            }
            let reg = core.get_or_insert_with(Registry::core);
            let fields = a.fields.iter().map(|f| {
                let (u, align) = reg.field_shape(&f.ty, &entry, a.memory)?;
                let stride = Field::stride(u, align);
                // A type of at most `2^24 - 1` bits takes at most 2^21
                // bytes, so a stride fits an immediate.
                debug_assert!(stride <= 1 << 21, "{stride}");
                Some((f.offset, stride as i32))
            });
            places.insert(a.name.as_str(), fields.collect());
        }
        Places(places)
    }
}

/// The offset of the field that `op` names, and its stride.
fn place(cx: &Cx<'_>, op: &Op) -> Result<(u64, i32), Unlowered> {
    let [Attr::Sym(s), Attr::Int(i)] = op.attrs.as_slice() else {
        return Err("fieldaddr takes a layout's symbol and a field's number".into());
    };
    let field = cx.places.0.get(s.as_str()).and_then(|fs| {
        let i = i.as_str().parse::<usize>().ok()?;
        fs.get(i).copied()
    });
    field.flatten().ok_or_else(|| {
        let sym = print_symbol(s);
        format!(
            "fieldaddr {sym} {} names no field that can be placed",
            i.as_str()
        )
        .into()
    })
}

/// `%q: ptr<N> = fieldaddr @s i %p` and `%q: ptr<N> = fieldaddr @s i %p, %k`.
fn field_addr(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([p, index @ ..], [q]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err("fieldaddr takes a pointer and an index and defines a pointer".into());
    };
    cx.width(&q.name)?;
    cx.width(p)?;
    let (offset, stride) = place(cx, op)?;
    cx.load(Reg::Rax, p)?;
    match index {
        [] => {}
        [k] => {
            memory::load_signed(cx, k)?;
            if stride != 1 {
                cx.asm.ins("imulq", format_args!("${stride}, %rcx, %rcx"));
            }
            cx.asm.ins("addq", format_args!("%rcx, %rax"));
        }
        _ => return Err("fieldaddr takes at most one index".into()),
    }
    // The offset is added modulo 2^64, where the address wraps, through
    // `%rcx` when it does not fit a displacement.
    match i32::try_from(offset as i64) {
        Ok(0) => {}
        Ok(d) => cx.asm.ins("leaq", format_args!("{d}(%rax), %rax")),
        Err(_) => {
            cx.asm.ins("movabsq", format_args!("${offset}, %rcx"));
            cx.asm.ins("addq", format_args!("%rcx, %rax"));
        }
    }
    cx.store(&q.name, Reg::Rax)
}

#[cfg(test)]
mod tests {
    use funk_ir::{Registry, parse};

    fn lowered(items: &str, func: &str) -> Result<String, Vec<funk_ir::Diagnostic>> {
        let text = format!("{items}\n\n{func}\n\nlocs {{\n  @0 = unknown\n}}\n");
        let m = parse(&text, &Registry::core()).unwrap();
        super::super::module(&m).map(|l| l.text)
    }

    const ROW: &str = "aggregate @row() memory(0) size(48) align(8) field(0, i32) \
                       field(8, i24, 4) field(24, float(15, 64)) field(40, ptr) {\n}";

    #[test]
    fn a_field_adds_its_offset_and_the_first_adds_nothing() {
        let asm = lowered(
            ROW,
            "func @f(%p: ptr) -> ptr, ptr {\n^entry:\n  %a: ptr = fieldaddr @row 0 %p @0\n  \
             %b: ptr = fieldaddr @row 3 %p @0\n  ret %a, %b @0\n}",
        )
        .unwrap();
        assert!(asm.contains("\tleaq\t40(%rax), %rax\n"), "{asm}");
        assert_eq!(asm.matches("leaq").count(), 1, "{asm}");
    }

    #[test]
    fn an_element_adds_its_index_read_as_signed_times_the_rounded_stride() {
        let asm = lowered(
            ROW,
            "func @f(%p: ptr, %k: i1, %l: i128) -> ptr, ptr {\n^entry:\n  \
             %a: ptr = fieldaddr @row 1 %p, %k @0\n  %b: ptr = fieldaddr @row 1 %p, %l @0\n  \
             ret %a, %b @0\n}",
        )
        .unwrap();
        // An `i24` takes 3 bytes, rounded up to its alignment of 4.
        let scaled = "\timulq\t$4, %rcx, %rcx\n\taddq\t%rcx, %rax\n\tleaq\t8(%rax), %rax\n";
        assert_eq!(asm.matches(scaled).count(), 2, "{asm}");
        assert!(
            asm.contains("\tshlq\t$63, %rcx\n\tsarq\t$63, %rcx\n\timulq"),
            "{asm}"
        );
    }

    #[test]
    fn an_offset_is_added_modulo_2_64_through_rcx_past_a_displacement() {
        let big = "aggregate @big() memory(0) size(18446744073709551615) align(8) \
                   field(0, i8, 4) field(2147483648, i64) field(18446744073709551600, i64) {\n}";
        let asm = lowered(
            big,
            "func @f(%p: ptr, %k: i64) -> ptr, ptr, ptr {\n^entry:\n  \
             %a: ptr = fieldaddr @big 1 %p @0\n  %b: ptr = fieldaddr @big 2 %p @0\n  \
             %c: ptr = fieldaddr @big 0 %p, %k @0\n  ret %a, %b, %c @0\n}",
        )
        .unwrap();
        assert!(
            asm.contains("\tmovabsq\t$2147483648, %rcx\n\taddq\t%rcx, %rax\n"),
            "{asm}"
        );
        // 2^64 - 16 is -16 modulo 2^64.
        assert!(asm.contains("\tleaq\t-16(%rax), %rax\n"), "{asm}");
        // An element of one byte needs no multiplication.
        assert!(!asm.contains("imulq"), "{asm}");
        let added = "\taddq\t%rcx, %rax\n\tmovq\t%rax, ";
        assert_eq!(asm.matches(added).count(), 2, "{asm}");
    }

    #[test]
    fn a_layout_of_a_memory_of_wider_units_is_reported_where_its_pointers_are_defined() {
        let ds = lowered(
            "layout memory(1, unit(16), pointer(32), little)\n\n\
             aggregate @w() memory(1) size(4) align(2) field(0, i16) field(2, i16) {\n}",
            "func @f(%p: ptr(1)) {\n^entry:\n  %a: ptr(1) = fieldaddr @w 1 %p @0\n  \
             ret @0\n}",
        )
        .unwrap_err();
        let at: Vec<_> = ds.iter().map(|d| d.message.split(':').next()).collect();
        assert_eq!(at, [Some("parameter %p"), Some("%a")], "{ds:?}");
        assert!(
            ds.iter()
                .all(|d| d.message.contains("memory 1 of 16-bit units"))
        );
    }
}
