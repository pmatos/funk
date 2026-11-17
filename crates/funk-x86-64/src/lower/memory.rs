//! Pointers and accesses: `ptradd`, `load` and `store`
//! (`dialects/core/pointer.rs`, `load.rs` and `store.rs` in `funk-ir`;
//! `docs/decisions/x86-64-backend-lowering-memory.md`).
//!
//! A pointer is a 64-bit address in one slot. The backend realises a
//! memory whose data layout entry has 8-bit units and 64-bit pointers, in
//! little-endian order, which x86-64 addresses directly: a unit is a byte,
//! an offset in units is an offset in bytes, and the units of a value are
//! its bytes in memory, least significant first. Every such memory shares
//! the process's address space, since no op turns a pointer of one memory
//! into a pointer of another. A value of a pointer of any other memory is
//! reported where it is defined, so no op of that memory is lowered.
//!
//! `ptradd` adds its offset, read as signed, to the address, which wraps
//! at 64 bits where the spec's offset does not; the two agree on every
//! access the spec allows (`docs/decisions/semantics-m1-memory.md#memory`).
//! An `i128` offset adds its low half, which is the same modulo 2^64.
//!
//! `load` and `store` move the value's units, `ceil(N / 8)` bytes for an
//! `iN` and 8 for a pointer, with one move, or two for an `i128`. A store
//! of an `i1` writes its byte as 0 or 1, the zero padding the human ruled
//! on 2026-11-11 (#231, Q2); a load of an `i1` reads its byte, whose bits
//! above bit 0 a value's bits above its width may be. Their `align(A)` and
//! ordering need no code: x86-64 accesses any address, a misaligned access
//! is UB in the spec, and M1's only ordering is `nonatomic`.

use funk_ir::ir::layout::memory;
use funk_ir::{MemLayout, Op};

use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;
use crate::width::{self, Class, Ext, PAIR};

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "ptradd" => Some(ptradd),
        "load" => Some(load),
        "store" => Some(store),
        _ => None,
    }
}

/// The entry of memory `n` in `layout` when the backend realises it: 8-bit
/// units and 64-bit pointers, in little-endian order; or why not.
pub fn realised(layout: &[MemLayout], n: u32) -> Result<MemLayout, String> {
    let e = memory(layout, n).ok_or_else(|| format!("the data layout declares no memory {n}"))?;
    if e.unit == 8 && e.pointer == width::POINTER && e.order == funk_ir::ByteOrder::Little {
        Ok(e)
    } else {
        Err(format!(
            "the x86-64 backend realises a memory of 8-bit units and 64-bit little-endian \
             pointers, not memory {n} of {}-bit units and {}-bit {} pointers",
            e.unit,
            e.pointer,
            e.order.word()
        ))
    }
}

/// `%q: ptr<N> = ptradd %p, %k`.
fn ptradd(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([p, k], [q]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err("ptradd takes a pointer and an integer and defines a pointer".into());
    };
    cx.width(&q.name)?;
    cx.width(p)?;
    let w = cx.width(k)?;
    cx.load(Reg::Rax, p)?;
    // The slot of an `i128` is that of its low half.
    cx.load(Reg::Rcx, k)?;
    if w != PAIR {
        width::extend(&mut cx.asm, Ext::Sign, w, Reg::Rcx);
    }
    cx.asm.ins("addq", format_args!("%rcx, %rax"));
    cx.store(&q.name, Reg::Rax)
}

/// The bits that one move of a `w`-bit value between memory and a
/// register moves: a byte for `i1`.
fn moved(w: u32) -> Result<u32, Unlowered> {
    match w {
        1 | 8 => Ok(8),
        16 | 32 | 64 => Ok(w),
        _ => Err(format!("an access of {w} bits is not one move").into()),
    }
}

/// `%v: T = load nonatomic [align(A)] %p`.
fn load(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([p], [v]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err("load takes a pointer and defines one value".into());
    };
    let w = cx.width(&v.name)?;
    if cx.class(&v.name)? == Class::Sse {
        return Err("the x86-64 backend does not lower a load of a float yet (#264)".into());
    }
    cx.width(p)?;
    cx.load(Reg::Rcx, p)?;
    if w == PAIR {
        cx.asm.ins("movq", format_args!("(%rcx), %rax"));
        cx.asm.ins("movq", format_args!("8(%rcx), %rdx"));
        return cx.store_pair(&v.name, Reg::Rax, Reg::Rdx);
    }
    let mnemonic = match moved(w)? {
        8 => "movzbl",
        16 => "movzwl",
        32 => "movl",
        _ => "movq",
    };
    let into = if mnemonic == "movq" { "%rax" } else { "%eax" };
    cx.asm.ins(mnemonic, format_args!("(%rcx), {into}"));
    cx.store(&v.name, Reg::Rax)
}

/// `store nonatomic [align(A)] %v, %p`.
fn store(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([v, p], []) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err("store takes a value and a pointer and defines nothing".into());
    };
    let w = cx.width(v)?;
    if cx.class(v)? == Class::Sse {
        return Err("the x86-64 backend does not lower a store of a float yet (#264)".into());
    }
    cx.width(p)?;
    cx.load(Reg::Rcx, p)?;
    if w == PAIR {
        cx.load_pair(Reg::Rax, Reg::Rdx, v)?;
        cx.asm.ins("movq", format_args!("%rax, (%rcx)"));
        cx.asm.ins("movq", format_args!("%rdx, 8(%rcx)"));
        return Ok(());
    }
    cx.load(Reg::Rax, v)?;
    if w == 1 {
        width::extend(&mut cx.asm, Ext::Zero, 1, Reg::Rax);
    }
    let bits = moved(w)?;
    let mnemonic = match bits {
        8 => "movb",
        16 => "movw",
        32 => "movl",
        _ => "movq",
    };
    cx.asm
        .ins(mnemonic, format_args!("{}, (%rcx)", Reg::Rax.at(bits)));
    Ok(())
}

#[cfg(test)]
mod tests {
    use funk_ir::{ByteOrder, MemLayout, Registry, parse};

    use super::*;

    fn lowered(text: &str) -> String {
        let m = parse(text, &Registry::core()).unwrap();
        super::super::module(&m).unwrap().text
    }

    fn body(func: &str) -> String {
        let text = format!("{func}\n\nlocs {{\n  @0 = unknown\n}}\n");
        lowered(&text)
    }

    #[test]
    fn memory_0_by_default_and_any_byte_memory_are_realised() {
        assert_eq!(realised(&[], 0), Ok(MemLayout::DEFAULT));
        let one = MemLayout {
            mem: 1,
            ..MemLayout::DEFAULT
        };
        assert_eq!(realised(&[one], 1), Ok(one));
        assert!(realised(&[], 1).is_err());
        for (unit, pointer, order) in [
            (16, 64, ByteOrder::Little),
            (8, 32, ByteOrder::Little),
            (8, 64, ByteOrder::Big),
        ] {
            let e = MemLayout {
                unit,
                pointer,
                order,
                ..MemLayout::DEFAULT
            };
            let why = realised(&[e], 0).unwrap_err();
            assert!(
                why.starts_with("the x86-64 backend realises a memory"),
                "{why}"
            );
        }
    }

    #[test]
    fn an_i1_is_stored_as_0_or_1_and_loaded_as_its_byte() {
        let asm = body(
            "func @f(%v: i1) -> i8 {\n^entry:\n  %p: ptr = alloca stack i8 @0\n  \
             store nonatomic %v, %p @0\n  %w: i8 = load nonatomic %p @0\n  ret %w @0\n}",
        );
        assert!(
            asm.contains("\tandl\t$1, %eax\n\tmovb\t%al, (%rcx)\n"),
            "{asm}"
        );
        assert!(asm.contains("\tmovzbl\t(%rcx), %eax\n"), "{asm}");
    }

    #[test]
    fn an_i128_moves_as_two_eightbytes_and_a_pointer_as_one() {
        let asm = body(
            "func @f(%v: i128, %q: ptr) -> i128, ptr {\n^entry:\n  \
             %p: ptr = alloca stack i128 @0\n  store nonatomic %v, %p @0\n  \
             %w: i128 = load nonatomic %p @0\n  %r: ptr = alloca stack ptr @0\n  \
             store nonatomic %q, %r @0\n  %s: ptr = load nonatomic align(1) %r @0\n  \
             ret %w, %s @0\n}",
        );
        for line in [
            "\tmovq\t%rax, (%rcx)\n\tmovq\t%rdx, 8(%rcx)\n",
            "\tmovq\t(%rcx), %rax\n\tmovq\t8(%rcx), %rdx\n",
            "\tmovq\t%rax, (%rcx)\n",
            "\tmovq\t(%rcx), %rax\n",
        ] {
            assert!(asm.contains(line), "{line}\n{asm}");
        }
    }

    #[test]
    fn a_load_or_store_of_a_float_is_reported() {
        for (func, why) in [
            (
                "func @f(%p: ptr) -> f32 {\n^entry:\n  %v: f32 = load nonatomic %p @0\n  \
                 ret %v @0\n}",
                "load of a float",
            ),
            (
                "func @f(%v: f64, %p: ptr) {\n^entry:\n  store nonatomic %v, %p @0\n  \
                 ret @0\n}",
                "store of a float",
            ),
        ] {
            let text = format!("{func}\n\nlocs {{\n  @0 = unknown\n}}\n");
            let m = parse(&text, &Registry::core()).unwrap();
            let Err(ds) = super::super::module(&m) else {
                panic!("a {why} is lowered");
            };
            assert_eq!(ds.len(), 1, "{ds:?}");
            assert!(ds[0].message.contains(why), "{ds:?}");
        }
    }

    #[test]
    fn ptradd_adds_its_offset_read_as_signed() {
        let asm = body(
            "func @f(%p: ptr, %k: i1, %l: i128) -> ptr {\n^entry:\n  \
             %q: ptr = ptradd %p, %k @0\n  %r: ptr = ptradd %q, %l @0\n  ret %r @0\n}",
        );
        assert!(
            asm.contains("\tshlq\t$63, %rcx\n\tsarq\t$63, %rcx\n\taddq\t%rcx, %rax\n"),
            "{asm}"
        );
        assert_eq!(asm.matches("\taddq\t%rcx, %rax\n").count(), 2, "{asm}");
    }

    #[test]
    fn a_pointer_of_a_memory_the_backend_does_not_realise_is_reported() {
        let text = "layout memory(0, unit(16), pointer(64), little)\n\n\
                    func @f(%p: ptr) -> i16 {\n^entry:\n  %v: i16 = load nonatomic %p @0\n  \
                    ret %v @0\n}\n\nlocs {\n  @0 = unknown\n}\n";
        let m = parse(text, &Registry::core()).unwrap();
        let Err(ds) = super::super::module(&m) else {
            panic!("a memory of 16-bit units is lowered");
        };
        assert_eq!(ds.len(), 1, "{ds:?}");
        assert!(ds[0].message.contains("memory 0 of 16-bit units"), "{ds:?}");
    }

    #[test]
    fn a_result_type_of_such_a_memory_is_reported_with_no_value_of_it() {
        let text = "layout memory(1, unit(16), pointer(64), little)\n\n\
                    func @f() -> ptr(1) {\n^entry:\n  unreachable @0\n}\n\n\
                    locs {\n  @0 = unknown\n}\n";
        let m = parse(text, &Registry::core()).unwrap();
        let Err(ds) = super::super::module(&m) else {
            panic!("a result of a memory of 16-bit units is lowered");
        };
        assert_eq!(ds.len(), 1, "{ds:?}");
        assert!(ds[0].message.starts_with("result 1: the x86-64"), "{ds:?}");
    }
}
