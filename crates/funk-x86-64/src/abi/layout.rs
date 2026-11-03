//! Where System V AMD64 passes the integer arguments of a call: in the six
//! argument registers, then on the stack (ADR-2026-10-30-1232,
//! ADR-2026-11-03-0108).
//!
//! An argument of one eightbyte, `i1` to `i64`, takes the next free
//! register, or else the next eightbyte of the stack. An `i128` takes the
//! next two registers when both are free. Otherwise it goes on the stack
//! whole, at the next offset that is a multiple of 16, and the register
//! left free, if any, goes to a later argument of one eightbyte. The stack
//! area is padded to a multiple of 16, so `%rsp` stays 16-byte aligned at
//! the call. gcc and clang lay out `__int128` arguments the same way.
//!
//! When a call's results go in memory, the address of the result area is
//! its first argument, of one eightbyte (ADR-2026-11-03-0109), as C passes
//! the address of a structure it returns in memory. The list that this
//! layout reads then starts with it (`abi::passed`), so it takes `%rdi`
//! and every argument after it moves along: an `i128` that would have had
//! `%r8` and `%r9` goes on the stack.
//!
//! The caller ([`super::call`]), the callee's prologue (`lower::func`), and
//! the entry's stack figure (`abi::pushed_words`) all read this one layout.

use super::ARG_REGS;
use crate::asm::Reg;

/// Where one eightbyte of an argument passes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Loc {
    /// In a register.
    Reg(Reg),
    /// On the stack, this many bytes above `%rsp` at the call.
    Stack(usize),
}

/// Where the arguments of a call pass.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    /// For each argument in order, where each of its eightbytes passes, the
    /// low one first.
    pub args: Vec<Vec<Loc>>,
    /// The bytes of the stack that the arguments take, padding included: a
    /// multiple of 16.
    pub stack: usize,
}

/// The layout of arguments of `words` eightbytes each, in order: 1 for a
/// value of at most 64 bits, 2 for an `i128`.
pub fn layout(words: &[usize]) -> Layout {
    let mut next = 0;
    let mut stack = 0usize;
    let mut args = Vec::with_capacity(words.len());
    for &n in words {
        debug_assert!(n == 1 || n == 2, "an argument has one or two eightbytes");
        if let Some(regs) = ARG_REGS.get(next..next + n) {
            args.push(regs.iter().map(|&r| Loc::Reg(r)).collect());
            next += n;
        } else {
            if n == 2 {
                stack = stack.next_multiple_of(16);
            }
            args.push((0..n).map(|k| Loc::Stack(stack + 8 * k)).collect());
            stack += 8 * n;
        }
    }
    Layout {
        args,
        stack: stack.next_multiple_of(16),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abi::passed;
    use Loc::Stack;
    use Reg::*;

    fn regs(rs: &[Reg]) -> Vec<Loc> {
        rs.iter().map(|&r| Loc::Reg(r)).collect()
    }

    #[test]
    fn six_eightbytes_go_in_registers_and_the_rest_on_the_stack() {
        assert_eq!(
            layout(&[]),
            Layout {
                args: vec![],
                stack: 0
            }
        );
        let l = layout(&[1; 8]);
        let want: Vec<Vec<Loc>> = [Rdi, Rsi, Rdx, Rcx, R8, R9]
            .iter()
            .map(|&r| regs(&[r]))
            .chain([vec![Stack(0)], vec![Stack(8)]])
            .collect();
        assert_eq!(
            l,
            Layout {
                args: want,
                stack: 16
            }
        );
        assert_eq!(layout(&[1; 7]).stack, 16);
        assert_eq!(layout(&[1; 9]).stack, 32);
    }

    /// Three `i128`s fill the six registers in pairs, low half first.
    #[test]
    fn an_i128_takes_two_registers_in_order() {
        let l = layout(&[2, 2, 2]);
        assert_eq!(
            l.args,
            [regs(&[Rdi, Rsi]), regs(&[Rdx, Rcx]), regs(&[R8, R9])]
        );
        assert_eq!(l.stack, 0);
        let l = layout(&[1, 2, 1]);
        assert_eq!(l.args, [regs(&[Rdi]), regs(&[Rsi, Rdx]), regs(&[Rcx])]);
    }

    /// The four layouts that gcc 16 and clang give these C prototypes, with
    /// `long` for one eightbyte and `__int128` for two.
    #[test]
    fn layouts_match_gcc_and_clang() {
        // g1(long a, b, c, d, e, __int128 x, long y): one register is left
        // for x, so x goes on the stack whole, and y takes %r9.
        let l = layout(&[1, 1, 1, 1, 1, 2, 1]);
        assert_eq!(l.args[5], [Stack(0), Stack(8)]);
        assert_eq!(l.args[6], regs(&[R9]));
        assert_eq!(l.stack, 16);
        // g2(long a, b, c, d, e, f, s, __int128 x, long t): x is aligned to
        // 16, past a hole after s.
        let l = layout(&[1, 1, 1, 1, 1, 1, 1, 2, 1]);
        assert_eq!(l.args[6], [Stack(0)]);
        assert_eq!(l.args[7], [Stack(16), Stack(24)]);
        assert_eq!(l.args[8], [Stack(32)]);
        assert_eq!(l.stack, 48);
        // g3(__int128 a, b, c, d, long e): d goes on the stack, then e.
        let l = layout(&[2, 2, 2, 2, 1]);
        assert_eq!(l.args[3], [Stack(0), Stack(8)]);
        assert_eq!(l.args[4], [Stack(16)]);
        assert_eq!(l.stack, 32);
        // g4(long a, __int128 b, c, d): %r9 is left over, and d goes on the
        // stack.
        let l = layout(&[1, 2, 2, 2]);
        assert_eq!(
            l.args[..3],
            [regs(&[Rdi]), regs(&[Rsi, Rdx]), regs(&[Rcx, R8])]
        );
        assert_eq!(l.args[3], [Stack(0), Stack(8)]);
        assert_eq!(l.stack, 16);
    }

    /// The layouts that gcc 16 and clang give these C prototypes, whose
    /// structure result goes in memory, so its address takes `%rdi` first.
    #[test]
    fn the_address_of_a_result_area_moves_the_arguments_along() {
        // s1 f(long a, b, c, d, __int128 x): x would have had %r8 and %r9;
        // with the address first, only %r9 is left, so x goes on the stack.
        assert_eq!(layout(&[1, 1, 1, 1, 2]).args[4], regs(&[R8, R9]));
        let l = layout(&passed(1, [1, 1, 1, 1, 2]));
        assert_eq!(l.args[0], regs(&[Rdi]));
        assert_eq!(l.args[4], regs(&[R8]));
        assert_eq!(l.args[5], [Stack(0), Stack(8)]);
        assert_eq!(l.stack, 16);
        // s2 f(__int128 a, b, long c, __int128 d): the address, a and b
        // take five registers; c takes %r9, and d goes on the stack.
        let l = layout(&passed(1, [2, 2, 1, 2]));
        assert_eq!(l.args[1..3], [regs(&[Rsi, Rdx]), regs(&[Rcx, R8])]);
        assert_eq!(l.args[3], regs(&[R9]));
        assert_eq!(l.args[4], [Stack(0), Stack(8)]);
        // s3 f(long a, b, c, d, e, __int128 x, long y): y has no register
        // left, and goes at 16, after x.
        let l = layout(&passed(1, [1, 1, 1, 1, 1, 2, 1]));
        assert_eq!(l.args[5], regs(&[R9]));
        assert_eq!(l.args[6], [Stack(0), Stack(8)]);
        assert_eq!(l.args[7], [Stack(16)]);
        assert_eq!(l.stack, 32);
        assert_eq!(passed(0, [2, 1]), [2, 1]);
    }

    #[test]
    fn an_i128_on_the_stack_is_aligned_to_16_wherever_it_falls() {
        let l = layout(&[2, 2, 2, 1, 2, 1, 2]);
        assert_eq!(l.args[3], [Stack(0)]);
        assert_eq!(l.args[4], [Stack(16), Stack(24)]);
        assert_eq!(l.args[5], [Stack(32)]);
        assert_eq!(l.args[6], [Stack(48), Stack(56)]);
        assert_eq!(l.stack, 64);
        let l = layout(&[2, 2, 2, 2, 2]);
        assert_eq!(l.args[4], [Stack(16), Stack(24)]);
        assert_eq!(l.stack, 32);
    }
}
