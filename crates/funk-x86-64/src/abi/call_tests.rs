//! Tests through the outgoing call interface: placement and its accounting.

use super::call;
use crate::asm::{Asm, Mem};

/// Walks the emitted call on distinct source slots. It checks the value
/// passed at each position, stack alignment at the call, the peak outgoing
/// space reported to stack reservation, and restoration after the call.
fn check_call(n: usize) {
    let args: Vec<Mem> = (0..n)
        .map(|k| Mem {
            disp: -8 * (k as i32 + 1),
        })
        .rev()
        .collect();
    let mut asm = Asm::new();
    let bytes = call(&mut asm, "1", &args).unwrap();
    let text = asm.finish();
    let mut below = 0u64;
    let mut peak = 0u64;
    let mut pushed = Vec::new();
    let mut registers = Vec::new();
    let mut called = false;
    for line in text.lines() {
        let (op, operands) = line.trim().split_once('\t').unwrap();
        match op {
            "subq" | "addq" => {
                assert!(operands.ends_with(", %rsp"), "{text}");
                let amount: u64 = operands[1..operands.len() - 6].parse().unwrap();
                if op == "subq" {
                    assert!(!called, "{text}");
                    below += amount;
                } else {
                    assert!(called, "{text}");
                    below -= amount;
                }
            }
            "pushq" => {
                assert!(!called, "{text}");
                below += 8;
                pushed.push(operands.to_string());
            }
            "movq" => {
                assert!(!called, "cleanup must preserve %rax: {text}");
                let (source, register) = operands.split_once(", ").unwrap();
                registers.push((source.to_string(), register.to_string()));
            }
            "call" => {
                assert!(!called, "{text}");
                assert_eq!(operands, "__funk_sym_31");
                assert_eq!(below % 16, 0, "{text}");
                assert_eq!(below, bytes, "{text}");
                called = true;
            }
            _ => panic!("unexpected op, such as an extension: {line}"),
        }
        peak = peak.max(below);
    }
    assert!(called);
    assert_eq!(below, 0, "outgoing space survives the call: {text}");
    assert_eq!(peak, bytes);
    let register_names = ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"];
    let expected: Vec<_> = args
        .iter()
        .zip(register_names)
        .map(|(slot, reg)| (slot.to_string(), reg.to_string()))
        .collect();
    assert_eq!(registers, expected);
    let expected: Vec<_> = args.iter().skip(6).rev().map(ToString::to_string).collect();
    assert_eq!(pushed, expected);
    assert_eq!(
        bytes,
        match n {
            0..=6 => 0,
            _ => ((n - 6) as u64).div_ceil(2) * 16,
        }
    );
}

#[test]
fn calls_place_arguments_and_report_exactly_the_space_they_restore() {
    for n in (0..=13).chain([511, 512, 513, 600]) {
        check_call(n);
    }
}

/// Extreme counts cannot be exercised with actual argument slots without
/// allocating GiB. Check the emitter's arithmetic at the encoding limit.
#[test]
fn outgoing_space_fits_the_cleanup_immediate_without_overflow() {
    let most = (i32::MAX as usize & !15) / 8 + 6;
    assert_eq!(super::outgoing_bytes(most), Some(i32::MAX & !15));
    assert_eq!(super::outgoing_bytes(most + 1), None);
    assert_eq!(super::outgoing_bytes(usize::MAX), None);
}
