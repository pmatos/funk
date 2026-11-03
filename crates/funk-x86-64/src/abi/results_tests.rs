//! Tests of the result convention: the layout, and the code of both sides.

use super::{Area, Layout, Place};
use crate::asm::{Asm, Mem, Reg};

fn layout(widths: &[u32]) -> (Vec<Place>, i32) {
    let l = Layout::new(widths).unwrap();
    (l.places().to_vec(), l.area())
}

fn area(offsets: &[i32]) -> Vec<Place> {
    offsets.iter().map(|&at| Place::Area(at)).collect()
}

#[test]
fn one_or_two_eightbytes_come_back_in_rax_then_rdx() {
    let (rax, rdx) = (Place::Reg(Reg::Rax), Place::Reg(Reg::Rdx));
    assert_eq!(layout(&[]), (vec![], 0));
    for w in [1, 8, 16, 32, 64] {
        assert_eq!(layout(&[w]), (vec![rax], 0));
        assert_eq!(layout(&[w, 64]), (vec![rax, rdx], 0));
        assert_eq!(layout(&[64, w]), (vec![rax, rdx], 0));
    }
    // One i128 alone: its low half in %rax, its high half in %rdx.
    assert_eq!(layout(&[128]), (vec![rax, rdx], 0));
    for widths in [&[][..], &[8], &[1, 64], &[128]] {
        let l = Layout::new(widths).unwrap();
        assert!(!l.in_memory());
        assert_eq!(l.hidden_arguments(), 0);
    }
}

#[test]
fn three_eightbytes_or_more_go_in_an_area_of_eightbytes() {
    assert_eq!(layout(&[8, 16, 1]), (area(&[0, 8, 16]), 32));
    assert_eq!(layout(&[64; 4]), (area(&[0, 8, 16, 24]), 32));
    let widths = [1, 8, 16, 32, 64, 1, 8, 16, 32];
    let offsets: Vec<i32> = (0..9).map(|k| 8 * k).collect();
    assert_eq!(layout(&widths), (area(&offsets), 80));
    let l = Layout::new(&[64, 64, 64]).unwrap();
    assert!(l.in_memory());
    assert_eq!(l.hidden_arguments(), 1);
}

/// An i128 among other results takes two eightbytes at a multiple of 16,
/// its low half first, as C lays out an `__int128` member.
#[test]
fn an_i128_among_several_results_is_16_byte_aligned_in_the_area() {
    assert_eq!(layout(&[64, 128]), (area(&[0, 16, 24]), 32));
    assert_eq!(layout(&[128, 64]), (area(&[0, 8, 16]), 32));
    assert_eq!(layout(&[128, 128]), (area(&[0, 8, 16, 24]), 32));
    assert_eq!(layout(&[1, 128, 8]), (area(&[0, 16, 24, 32]), 48));
    assert_eq!(layout(&[8, 16, 128]), (area(&[0, 8, 16, 24]), 32));
}

#[test]
fn a_type_the_backend_does_not_lower_counts_as_one_eightbyte() {
    let types: Vec<funk_ir::Type> = ["i7", "i64", "i33"]
        .iter()
        .map(|t| funk_ir::Type::word(*t))
        .collect();
    let l = Layout::of_types(&types).unwrap();
    assert_eq!(l.places(), area(&[0, 8, 16]));
}

fn slots(n: usize) -> Vec<Mem> {
    (1..=n)
        .map(|k| Mem {
            disp: -8 * k as i32,
        })
        .collect()
}

fn code(f: impl FnOnce(&mut Asm)) -> String {
    let mut asm = Asm::new();
    f(&mut asm);
    asm.finish()
}

#[test]
fn ret_gives_results_in_registers_and_an_i1_as_0_or_1() {
    let l = Layout::new(&[1, 8]).unwrap();
    let s = slots(2);
    let given = code(|a| l.give(a, None, &[(s[0], 1), (s[1], 8)]).unwrap());
    assert_eq!(
        given,
        "\tmovq\t-8(%rbp), %rax\n\tandl\t$1, %eax\n\tmovq\t-16(%rbp), %rdx\n"
    );
    let given = code(|a| l.give(a, None, &[(s[0], 64), (s[1], 1)]).unwrap());
    assert_eq!(
        given,
        "\tmovq\t-8(%rbp), %rax\n\tmovq\t-16(%rbp), %rdx\n\tandl\t$1, %edx\n"
    );
    let one = Layout::new(&[32]).unwrap();
    assert_eq!(
        code(|a| one.give(a, None, &[(s[0], 32)]).unwrap()),
        "\tmovq\t-8(%rbp), %rax\n"
    );
    let none = Layout::new(&[]).unwrap();
    assert_eq!(code(|a| none.give(a, None, &[]).unwrap()), "");
}

#[test]
fn ret_writes_results_in_memory_and_returns_the_area_s_address() {
    let l = Layout::new(&[16, 1, 64]).unwrap();
    let s = slots(4);
    let from = [(s[0], 16), (s[1], 1), (s[2], 64)];
    let given = code(|a| l.give(a, Some(s[3]), &from).unwrap());
    assert_eq!(
        given,
        "\tmovq\t-32(%rbp), %rax\n\
         \tmovq\t-8(%rbp), %rcx\n\tmovq\t%rcx, 0(%rax)\n\
         \tmovq\t-16(%rbp), %rcx\n\tandl\t$1, %ecx\n\tmovq\t%rcx, 8(%rax)\n\
         \tmovq\t-24(%rbp), %rcx\n\tmovq\t%rcx, 16(%rax)\n"
    );
    assert!(l.give(&mut Asm::new(), None, &from).is_err());
    assert!(l.give(&mut Asm::new(), Some(s[3]), &from[..2]).is_err());
}

#[test]
fn a_caller_stores_each_result_as_it_comes() {
    let s = slots(3);
    let two = Layout::new(&[1, 16]).unwrap();
    assert_eq!(
        code(|a| two.receive(a, None, &s[..2]).unwrap()),
        "\tmovq\t%rax, -8(%rbp)\n\tmovq\t%rdx, -16(%rbp)\n"
    );
    let three = Layout::new(&[8, 8, 8]).unwrap();
    let area = Area {
        address: Mem { disp: -32 },
        base: Mem { disp: -64 },
    };
    assert_eq!(
        code(|a| three.pass(a, area)),
        "\tleaq\t-64(%rbp), %rax\n\tmovq\t%rax, -32(%rbp)\n"
    );
    assert_eq!(
        code(|a| three.receive(a, Some(area), &s).unwrap()),
        "\tmovq\t-64(%rbp), %rax\n\tmovq\t%rax, -8(%rbp)\n\
         \tmovq\t-56(%rbp), %rax\n\tmovq\t%rax, -16(%rbp)\n\
         \tmovq\t-48(%rbp), %rax\n\tmovq\t%rax, -24(%rbp)\n"
    );
    let mut asm = Asm::new();
    assert!(three.receive(&mut asm, None, &s).is_err());
    assert_eq!(asm.finish(), "", "a failed receive appends nothing");
}

/// The area's size and every offset fit a signed 32-bit displacement.
#[test]
fn an_area_beyond_2_gib_is_refused() {
    assert_eq!(super::fits(i32::MAX as u64), Ok(i32::MAX));
    assert!(super::fits(1 << 31).is_err());
}
