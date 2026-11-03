# The i128 division helper is hand-written assembly that each module's object file carries, under local __funk_rt_ symbols

Status: accepted

## Context

S2 puts `i128` in the M0 backend, with division through a runtime helper
(ADR-2026-10-29-2007). x86-64 has no instruction that divides 128 bits by
128 bits: `divq` and `idivq` divide 128 bits by 64, and trap when the
quotient does not fit in 64. [#22](https://github.com/pmatos/funk/issues/22)
lowers `sdiv`, `udiv`, `srem` and `urem` at `i128` as calls of such a
helper, and leaves to an ADR how it is built, shipped and linked, and how
its symbol stays apart from the module's.

- `funk build` assembles two files (ADR-2026-10-30-1229): the module's
  functions, which become `OUTPUT.o`, and the entry point with its
  runtime, `runtime.s` and `values.s`, which only the executable gets.
  C code may link `OUTPUT.o` and call its functions (ADR-2026-10-30-1232).
- ADR-2026-10-30-1230 rejected a stack probe routine such as `__chkstk`
  because C code that links the object file would have to provide it.
- Any string is a fir symbol (ADR-2026-10-29-2012). `abi::symbol` spells
  a word that starts with a letter as itself, and every other name as
  `__funk_sym_` and its bytes in hexadecimal (ADR-2026-10-30-1232).
- Two object files from `funk build` can be linked into one C program.

## Decision

- **Hand-written assembly in the backend.** The helper is
  [`crates/funk-x86-64/src/lower/div128.s`](../../crates/funk-x86-64/src/lower/div128.s),
  GNU `as` assembly in AT&T syntax, which the backend holds as text with
  `include_str!`, as it holds the entry's runtime. It has one routine per
  op, `__funk_rt_sdiv128`, `__funk_rt_udiv128`, `__funk_rt_srem128` and
  `__funk_rt_urem128`, and two that they share, `__funk_rt_udivmod128`
  and `__funk_rt_magnitudes`. ADR-2026-11-03-0415 says how they are
  called and how they divide.
- **Shipped in the module's object file.** `lower::module` appends the
  file, once, to the module's assembly, after its functions, when a
  function of the module divides at `i128`. Any other module's assembly
  is as before. `funk build` assembles and links the same two files as
  before, and the executable gets the helper through `OUTPUT.o`.
- **Local symbols that start with `__funk_rt_`.** No routine is `.globl`,
  so each is a local symbol of the object file that holds it: `as` binds
  each call of it in that file, and no other object file sees it. No fir
  function's symbol starts with `__funk_rt_`: a word symbol starts with a
  letter, and every other symbol starts with `__funk_sym_`. So a function
  named `@__funk_rt_sdiv128`, a word that starts with `_`, has the symbol
  `__funk_sym_5f5f66756e6b5f72745f73646976313238`. The routines' labels
  start with `.Lrt_div128_`, which no label of a block (`.Lb`) or other
  local label (`.Lc`) of a function does.

## Alternatives

- **The helper in the entry's runtime.** `OUTPUT.o` would then hold an
  undefined symbol, which C code that links it would have to provide.
- **A separate object file or archive** that `funk build` links. The same
  gap for C code, and one more file to ship and find.
- **libgcc's `__divti3`, `__udivti3`, `__modti3` and `__umodti3`.** funk
  links no libc and no libgcc (ADR-2026-10-30-1229), so its own
  executables would lack them.
- **Global symbols.** Two object files that both divide at `i128` would
  each define them, and a C program that links both would fail to link.
- **The helper in every module.** Its bytes in every object file, most of
  which never divide at `i128`, and a change to every module's assembly.
- **The routine's code inline at each division.** Its loop and branches
  at every division, where a call is seven instructions.

## Consequences

- `OUTPUT.o` stands alone: C code that links it needs no runtime library
  for division at `i128`.
- Each object file that divides at `i128` holds its own copy of the
  helper, a few hundred bytes.
- A function of the module may have a routine's name; a native test and
  the corpus module `div-symbol-i128` build and run one.
- The helper is hand-written code, so the corpus checks it against
  `fir-ref` as it checks every lowering, and native tests check it
  against Rust's `i128` and `u128` arithmetic.
- This refines ADR-2026-10-30-1229: the module's assembly file may end
  with the helper.
