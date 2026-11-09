# LLVM test cases are chosen for M0's ops and rewritten into fir by fixed rules

Status: accepted; refined by ADR-2026-11-03-1614 and ADR-2026-11-03-1619
Tier: implementation; area: testing-and-harness

## Context

[#23](https://github.com/pmatos/funk/issues/23) asks for LLVM test cases
ported to fir: integer edge cases from instruction simplification and x86
code generation, written in fir's text as the spec gives it. LLVM IR has
much that fir does not: `undef`, a poison constant, phis, vectors, memory,
floating point, intrinsics, and flags on ops that fir's ops do not have.
An LLVM test states a fold, an input and the output that a pass makes of
it, as CHECK lines; a code generation test's CHECK lines are assembly.
ADR-2026-11-03-0643 says where the ported cases live and how each names
its source.

## Decision

**Choice.** A case can come in when fir's M0 ops can express it and it
tests an integer edge case: flags and poison, shifts by the width or
more, division and remainder by 0 and of the signed minimum by -1,
comparisons, width changes, `select` and `freeze`, wide and odd widths,
and `i128`. The sources are `Transforms/InstSimplify/`,
`Transforms/InstCombine/`'s `apint-*` and `div-i1` tests, and
`CodeGen/X86/`'s tests of `i128`, division and shifts. A function that
uses a vector, floating point, a pointer, memory, a call to a function
that its file does not define, an intrinsic, `switch` or `undef` is left
out, and so is one whose name the repository's spelling check rejects,
as the port keeps LLVM's names and an exception to that check is a human
call. From each file the port takes each kind of fold, each negative test
that shows a flag or a bound at work, and every case at an odd width, of
a parameter, a result or a value in between, or at `i128`; a function
that repeats one of those with other constants, commuted operands or
another predicate is left out, and so most of a large file, such as
`select.ll`, is.

**Rewrites.**

- Unreachable blocks are deleted, phis become block arguments, and labels
  are written `^name`. LLVM's names of functions and blocks are kept, and
  so are most of its names of values. Where a port names a value anew,
  as a template that writes many functions does, it does not use a name
  that LLVM gives another value of the function.
- A constant operand becomes a `const` op. `i1` constants are `true` and
  `false`; comparisons are `icmp slt %a, %b`; constants take fir's signed
  spelling, so LLVM's unsigned `i64 13835058055282163710` is
  `-4611686018427387906`.
- A poison constant becomes `%p = shl %n, %n`, with `%n` the width, which
  the spec makes poison on every run.
- A flag that fir's op does not have (`shl nuw`, `zext nneg`,
  `or disjoint`) is dropped only where it can never give poison in that
  function, and the sidecar says why. Where it can, the function is left
  out, as are `lshr exact`, `ashr exact` and the other shift flags.
- A result that a code generation test stores through a pointer is
  returned, a struct of two values is two results, and parameter and
  function attributes are dropped.

**Tests.** Each fold becomes runs of the input function at chosen
arguments: boundary bit patterns, and values at the edge of the fold's
condition. A run expects the folded value where the input is defined, and
the input's poison or UB where it is not, which LLVM's value refines.
Where the folded form has ops, it is ported too, as `@NAME.folded`, and
runs on the same arguments; where a file has only a RUN line, the folded
form is the one that it asks for, written by hand. A negative test, one
that LLVM does not fold, runs on an argument where the fold would be
wrong, if there is one. A negative test, and a code generation test,
whose CHECK lines are assembly, declares the value that its IR computes,
worked out apart from `fir-ref`. Every expected value comes from LLVM's
statement or from that working, not from a run of `fir-ref`, so a run
that disagrees fails. A run whose module builds and whose result is a
value is differential and declares that one result, so `fir-ref` must
give it and native code must refine it; a run that gives poison or UB,
or whose module has a width the backend does not lower, is
interpreter-only.

**Where fir and LLVM differ.** `fir-ref` gave LLVM's stated result on
every run, or poison or UB that LLVM's result refines. LLVM's CHECK
lines fold some divisions that are UB to poison, where `fir-ref`
reports UB: `sdiv i8 -128, -1` and `srem i8 -128, -1`, in `div.ll`'s
`@sdiv_minusone_divisor` and `rem.ll`'s `@srem_minusone_divisor`, and
the division by a `false` that both paths give in `div-i1.ll`'s four
`@*_by_zero_indirect_is_poison` functions. LangRef makes these
divisions UB too, so the poison is LLVM's refinement of that UB, not a
difference of semantics.

## Consequences

- Each sidecar's comment says which rewrites its cases needed and which
  of its file's functions are left out.
- A later dialect with vectors, memory or more flags can bring the
  left-out functions in under the same rules.
- The folded forms are hand translations of CHECK lines, so a change in
  LLVM's output does not reach them until a module is ported again.
