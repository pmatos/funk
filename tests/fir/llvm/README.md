# Test cases ported from LLVM

The `.fir` modules and `.toml` sidecars of this directory are derived from
test files of the LLVM Project, <https://github.com/llvm/llvm-project>,
read at commit `7a941dfb2877a0b8cf30323fefa85ad019e0b0f5` (the tag
`llvmorg-23.1.4`). They were changed: each case was translated by hand
from LLVM IR into fir, and runs of it were added as tests. Each sidecar
names the LLVM test file it comes from, and each of its tests the LLVM
function, or the CHECK or RUN lines of that file, that the test's
function is.

The LLVM Project is under the Apache License v2.0 with LLVM Exceptions
(`Apache-2.0 WITH LLVM-exception`). Its licence, copied from
`llvm/LICENSE.TXT` at that commit, is in [`LICENSE.TXT`](LICENSE.TXT)
beside this file. Only the empty line that ends LLVM's file is gone, as
the repository's `end-of-file-fixer` check removes it, and the harness
checks that the copy is that licence. The files of this
directory are distributed under that licence, not under funk's MIT
licence.

[ADR-2026-11-03-0643](../../../docs/adrs/2026-11-03-0643-ported-llvm-tests-keep-llvm-s-licence-and-name-their-source.md)
decides this layout and how the licence is kept, and
[ADR-2026-11-03-0644](../../../docs/adrs/2026-11-03-0644-llvm-cases-are-chosen-for-m0-s-ops-and-rewritten-by-fixed-rules.md)
how the cases were chosen and rewritten.

## How the cases were rewritten

- Every block is reachable, as fir requires; LLVM's phis are block
  arguments, and its labels are written `^name`.
- A constant operand is a `const` op. An `i1` constant is `true` or
  `false`, a comparison is `icmp slt %a, %b`, and a constant is written
  in fir's signed spelling: LLVM's `i64 13835058055282163710` is
  `-4611686018427387906`.
- fir has no `undef`: a case that rests on it is left out. LLVM's
  `poison` constant is fir's op `poison`, as in `%p: i32 = poison`
  (ADR-2026-11-03-1619). Until #122 gave fir that op, a case wrote it as
  `%p = shl %n, %n` with `%n` the width, which is poison.
- A flag that fir does not have, such as `shl nuw`, `zext nneg` or
  `or disjoint`, is dropped only where it can never give poison, and
  the sidecar says why; otherwise the case is left out.
- A result that a code generation test stores through a pointer is
  returned instead, and a struct of two values is two results.
- LLVM's names of functions are kept, but a word that the repository's
  spelling check rejects is spelled correctly
  ([ADR-2026-11-03-1614](../../../docs/adrs/2026-11-03-1614-a-ported-llvm-name-that-fails-the-spelling-check-is-corrected.md)).
- Vectors, floating point, pointers, memory, calls to functions that the
  file does not define, intrinsics and `switch` are left out.

Where LLVM folds a function, its tests expect the folded value; where the
input gives poison or UB, the test expects that, and the sidecar says how
LLVM's value refines it. Where the folded form has ops, it is ported too,
as `@NAME.folded`, and runs on the same arguments. A test is
differential, and declares its one result, where its module builds and
the result is a value; otherwise it is interpreter-only. Each sidecar's
comment says what its cases show and which of the file's functions are
left out.

## Sidecars

A ported module's sidecar has the keys of the corpus's format
([`../README.md`](../README.md)) and two more, both required, which the
harness checks:

```toml
source = { file = "llvm/test/Transforms/InstSimplify/shift.ll", commit = "7a941dfb2877a0b8cf30323fefa85ad019e0b0f5" }
tests = [
  { func = "@shl_by_bitwidth", args = ["5"], expect = ["poison"], from = "@shl_by_bitwidth" },
  { func = "@shl_or_shr.folded", args = ["5", "7"], results = [{ values = ["5"], witness = [] }], from = "@shl_or_shr, its CHECK lines" },
]
```

- `source` names the LLVM test file, by its path in llvm-project, and the
  full hash of the commit it was read at. Every module names the same
  commit.
- `from` names the LLVM function, or its CHECK lines, or the file's RUN
  line, that the test's function is. Where the test's function corrects
  the spelling of LLVM's name, `from` names it by its file and lines.

Each function's ops carry a location that names the LLVM file and the
lines of the function, of its CHECK lines or of the file's RUN line that
they come from, so
each `.fir` text says, in its own canonical form, that it is derived from
LLVM.

## Modules

| Module | LLVM test | Functions | Differential | Interpreter-only |
| --- | --- | ---: | ---: | ---: |
| `instcombine-apint-add` | `llvm/test/Transforms/InstCombine/apint-add.ll` | 16 | 0 | 86 |
| `instcombine-apint-div1` | `llvm/test/Transforms/InstCombine/apint-div1.ll` | 6 | 0 | 32 |
| `instcombine-apint-div2` | `llvm/test/Transforms/InstCombine/apint-div2.ll` | 6 | 0 | 32 |
| `instcombine-apint-mul1` | `llvm/test/Transforms/InstCombine/apint-mul1.ll` | 2 | 0 | 14 |
| `instcombine-apint-rem1` | `llvm/test/Transforms/InstCombine/apint-rem1.ll` | 6 | 0 | 32 |
| `instcombine-apint-rem2` | `llvm/test/Transforms/InstCombine/apint-rem2.ll` | 6 | 0 | 32 |
| `instcombine-apint-shift-simplify` | `llvm/test/Transforms/InstCombine/apint-shift-simplify.ll` | 6 | 0 | 24 |
| `instcombine-div-i1` | `llvm/test/Transforms/InstCombine/div-i1.ll` | 8 | 6 | 26 |
| `instsimplify-2010-12-20-Boolean` | `llvm/test/Transforms/InstSimplify/2010-12-20-Boolean.ll` | 4 | 8 | 0 |
| `instsimplify-cast` | `llvm/test/Transforms/InstSimplify/cast.ll` | 2 | 5 | 0 |
| `instsimplify-cmp_ext` | `llvm/test/Transforms/InstSimplify/cmp_ext.ll` | 18 | 68 | 0 |
| `instsimplify-div` | `llvm/test/Transforms/InstSimplify/div.ll` | 27 | 53 | 37 |
| `instsimplify-exact-nsw-nuw` | `llvm/test/Transforms/InstSimplify/exact-nsw-nuw.ll` | 3 | 13 | 2 |
| `instsimplify-freeze` | `llvm/test/Transforms/InstSimplify/freeze.ll` | 11 | 33 | 0 |
| `instsimplify-icmp-constant` | `llvm/test/Transforms/InstSimplify/icmp-constant.ll` | 30 | 68 | 15 |
| `instsimplify-rem-widths` | `llvm/test/Transforms/InstSimplify/rem.ll` | 1 | 0 | 6 |
| `instsimplify-rem` | `llvm/test/Transforms/InstSimplify/rem.ll` | 34 | 79 | 29 |
| `instsimplify-sdiv` | `llvm/test/Transforms/InstSimplify/sdiv.ll` | 6 | 12 | 10 |
| `instsimplify-select-widths` | `llvm/test/Transforms/InstSimplify/select.ll` | 3 | 0 | 18 |
| `instsimplify-select` | `llvm/test/Transforms/InstSimplify/select.ll` | 36 | 112 | 4 |
| `instsimplify-shift-widths` | `llvm/test/Transforms/InstSimplify/shift.ll` | 5 | 0 | 25 |
| `instsimplify-shift` | `llvm/test/Transforms/InstSimplify/shift.ll` | 17 | 33 | 21 |
| `instsimplify-signed-div-rem-sdiv` | `llvm/test/Transforms/InstSimplify/signed-div-rem.ll` | 16 | 63 | 1 |
| `instsimplify-signed-div-rem-srem` | `llvm/test/Transforms/InstSimplify/signed-div-rem.ll` | 11 | 44 | 0 |
| `instsimplify-srem` | `llvm/test/Transforms/InstSimplify/srem.ll` | 3 | 12 | 3 |
| `x86-divide-by-constant-i64` | `llvm/test/CodeGen/X86/divide-by-constant.ll` | 21 | 105 | 0 |
| `x86-divide-by-constant-narrow` | `llvm/test/CodeGen/X86/divide-by-constant.ll` | 13 | 74 | 0 |
| `x86-divrem` | `llvm/test/CodeGen/X86/divrem.ll` | 8 | 44 | 12 |
| `x86-i128-add` | `llvm/test/CodeGen/X86/i128-add.ll` | 1 | 6 | 0 |
| `x86-i128-mul` | `llvm/test/CodeGen/X86/i128-mul.ll` | 1 | 6 | 0 |
| `x86-i128-sdiv` | `llvm/test/CodeGen/X86/i128-sdiv.ll` | 3 | 24 | 0 |
| `x86-i128-udiv` | `llvm/test/CodeGen/X86/i128-udiv.ll` | 10 | 60 | 0 |
| `x86-legalize-shift-64` | `llvm/test/CodeGen/X86/legalize-shift-64.ll` | 4 | 44 | 0 |
| `x86-shift-i128` | `llvm/test/CodeGen/X86/shift-i128.ll` | 10 | 51 | 24 |
| All 34 modules | | 354 | 1023 | 485 |
