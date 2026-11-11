//! Tests through the outgoing call interface: placement and its accounting.

use super::{Arg, Loc, call, layout};
use crate::asm::{Asm, Mem};
use crate::width::Class;

/// [`check_classes`] on integer arguments of `words` eightbytes each.
fn check_call(words: &[usize]) {
    let classes: Vec<Class> = words
        .iter()
        .map(|&w| if w == 2 { Class::Pair } else { Class::Int })
        .collect();
    check_classes(&classes);
}

/// Walks the emitted call on distinct source slots, for arguments of the
/// classes `classes`. It checks the eightbyte passed at each place of the
/// layout, register or stack, that the rest of the stack area is padding,
/// stack alignment at the call, the peak outgoing space reported to stack
/// reservation, and restoration after the call.
fn check_classes(classes: &[Class]) {
    let mut used = 0;
    let args: Vec<Arg> = classes
        .iter()
        .map(|&class| {
            used += class.words();
            Arg {
                slot: Mem {
                    disp: -8 * used as i32,
                },
                class,
            }
        })
        .collect();
    let mut asm = Asm::new();
    let bytes = call(&mut asm, "1", &args).unwrap();
    let text = asm.finish();
    let mut below = 0u64;
    let mut peak = 0u64;
    // The eightbytes put below the caller's `%rsp`, from the top down:
    // `None` for padding.
    let mut pushed: Vec<Option<String>> = Vec::new();
    let mut registers = Vec::new();
    let mut at_call = None;
    for line in text.lines() {
        let (op, operands) = line.trim().split_once('\t').unwrap();
        match op {
            "subq" | "addq" => {
                assert!(operands.ends_with(", %rsp"), "{text}");
                let amount: u64 = operands[1..operands.len() - 6].parse().unwrap();
                if op == "subq" {
                    assert!(at_call.is_none(), "{text}");
                    assert_eq!(amount % 8, 0, "{text}");
                    below += amount;
                    pushed.extend((0..amount / 8).map(|_| None));
                } else {
                    assert!(at_call.is_some(), "{text}");
                    below -= amount;
                }
            }
            "pushq" => {
                assert!(at_call.is_none(), "{text}");
                below += 8;
                pushed.push(Some(operands.to_string()));
            }
            "movq" => {
                assert!(at_call.is_none(), "cleanup must preserve %rax: {text}");
                let (source, register) = operands.split_once(", ").unwrap();
                registers.push((register.to_string(), source.to_string()));
            }
            "call" => {
                assert!(at_call.is_none(), "{text}");
                assert_eq!(operands, "__funk_sym_31");
                assert_eq!(below % 16, 0, "{text}");
                assert_eq!(below, bytes, "{text}");
                at_call = Some(pushed.clone());
            }
            _ => panic!("unexpected op, such as an extension: {line}"),
        }
        peak = peak.max(below);
    }
    let at_call = at_call.expect("the call is made");
    assert_eq!(below, 0, "outgoing space survives the call: {text}");
    assert_eq!(peak, bytes);
    let layout = layout(classes);
    assert_eq!(bytes, layout.stack as u64);
    // The eightbyte `at` bytes above `%rsp` at the call is the one pushed
    // `at / 8` places before the last.
    let mut stack: Vec<Option<String>> = at_call.into_iter().rev().collect();
    let mut expected_registers = Vec::new();
    for (a, locs) in args.iter().zip(&layout.args) {
        assert_eq!(locs.len(), a.class.words());
        for (loc, slot) in locs.iter().zip([a.slot, a.slot.high()]) {
            match *loc {
                Loc::Reg(r) => expected_registers.push((r.q().to_string(), slot.to_string())),
                Loc::Xmm(n) => expected_registers.push((format!("%xmm{n}"), slot.to_string())),
                Loc::Stack(at) => {
                    let got = stack[at / 8].take();
                    assert_eq!(got, Some(slot.to_string()), "at {at}: {text}");
                }
            }
        }
    }
    assert!(stack.iter().all(Option::is_none), "{stack:?}: {text}");
    assert_eq!(registers, expected_registers, "{text}");
    if classes.iter().all(|&c| c == Class::Int) {
        let n = classes.len();
        assert_eq!(
            bytes,
            match n {
                0..=6 => 0,
                _ => ((n - 6) as u64).div_ceil(2) * 16,
            }
        );
    }
}

#[test]
fn calls_place_arguments_and_report_exactly_the_space_they_restore() {
    for n in (0..=13).chain([511, 512, 513, 600]) {
        check_call(&vec![1; n]);
    }
}

/// Arguments of one and two eightbytes, mixed: every pattern of up to 10
/// arguments, and longer ones drawn from a fixed sequence.
#[test]
fn calls_of_i128_arguments_place_both_halves_where_the_layout_says() {
    for n in 0..=10u32 {
        for bits in 0..1u32 << n {
            let words: Vec<usize> = (0..n).map(|k| 1 + ((bits >> k) & 1) as usize).collect();
            check_call(&words);
        }
    }
    let mut seed = 0x9e37_79b9_7f4a_7c15_u64;
    for _ in 0..200 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        let n = 11 + (seed % 40) as usize;
        let words: Vec<usize> = (0..n)
            .map(|k| 1 + ((seed >> (k % 64)) & 1) as usize)
            .collect();
        check_call(&words);
    }
}

/// Integers, `i128`s and floats, mixed: every pattern of up to 7 arguments,
/// and runs of floats past the eight SSE registers.
#[test]
fn calls_of_float_arguments_place_them_where_the_layout_says() {
    let all = [Class::Int, Class::Pair, Class::Sse];
    for n in 0..=7u32 {
        for code in 0..3usize.pow(n) {
            let classes: Vec<Class> = (0..n).map(|k| all[code / 3usize.pow(k) % 3]).collect();
            check_classes(&classes);
        }
    }
    for n in [8, 9, 10, 17] {
        check_classes(&vec![Class::Sse; n]);
        let mut mixed = vec![Class::Int; 7];
        mixed.extend(vec![Class::Sse; n]);
        mixed.push(Class::Pair);
        check_classes(&mixed);
    }
}

/// Extreme sizes cannot be exercised with actual argument slots without
/// allocating GiB. Check the emitter's arithmetic at the encoding limit.
#[test]
fn outgoing_space_fits_the_cleanup_immediate_without_overflow() {
    let most = i32::MAX as usize & !15;
    assert_eq!(super::outgoing_bytes(most), Some(i32::MAX & !15));
    assert_eq!(super::outgoing_bytes(most + 16), None);
    assert_eq!(super::outgoing_bytes(usize::MAX), None);
}
