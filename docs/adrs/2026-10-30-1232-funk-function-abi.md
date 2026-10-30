# A funk function is a System V AMD64 function, with a symbol made from its fir name

Status: accepted

## Context

The object file that `funk build` writes holds the module's functions
([#12](https://github.com/pmatos/funk/issues/12)). Its own entry point calls
them, #20 adds calls between them, and C code may call them too. A fir
symbol may be any string, such as `@"a b"` or `@""`
(ADR-2026-10-29-2012), but an assembler and an ELF symbol table cannot take
every string, and the toolchain defines some names itself: `ld` defines
`_end` and `__bss_start`, and `as` treats `_GLOBAL_OFFSET_TABLE_` apart.
Returning more than one value needs a convention of its own, which #31
decides (ADR-2026-10-30-0816).

## Decision

- **System V AMD64.** Every fir function is a global function symbol
  (`.globl`, `@function`). Integer arguments go in `%rdi`, `%rsi`,
  `%rdx`, `%rcx`, `%r8` and `%r9`, then on the stack, 8 bytes each, the
  seventh at `8(%rsp)` on entry. `%rsp` is 16-byte aligned at each call. A
  result goes in `%rax`. `%rbx`, `%rbp` and `%r12` to `%r15` are
  callee-saved.
- **Widths at the boundary.** A funk function reads only the low `N` bits
  of each `iN` argument; the bits above are unspecified
  (ADR-2026-10-30-1231). It returns an `iN` result in the low `N` bits of
  `%rax`, with the bits above unspecified, except that it returns an `i1`
  result as 0 or 1 in all of `%rax`. That is more than C gives for a
  `_Bool` result, which defines only bits 0 to 7 (bit 0 is the value, bits
  1 to 7 are zero), so code that calls a C function may rely only on bit
  0, or on `%al` read as 0 or 1.
- **Calling code that funk did not compile.** C callees expect more of a
  narrow argument than a funk callee does. clang reads an `i8` or `i16`
  argument as extended to 32 bits by the sign of its C type, and gcc and
  clang both read a `_Bool` argument as 0 or 1 in its low 8 bits. A slot
  after `add` can hold neither (127 + 1 at `i8` leaves 128; `true + true`
  at `i1` leaves 2). So a funk call to such code must extend an `i8` or
  `i16` argument to 32 bits as the callee's C type requires (by sign for a
  signed type, by zero for an unsigned one), and pass an `i1` as 0 or 1 in
  at least its low 8 bits. fir types carry no sign, so such a call needs a
  sign- or zero-extension marker on each narrow parameter. #20, which adds
  calls, decides what a funk caller extends, and must define that marker
  before funk calls code it did not compile.
- **Results.** A function returns no value or one value. One with more is
  reported at its `ret` until #31 gives the convention for more.
- **Symbols.** A fir name that is a word starting with a letter (letters,
  digits, `_` and `.`) is its own symbol. Every other name, including
  every name that starts with `_`, is `__funk_sym_` followed by its UTF-8
  bytes in lower-case hexadecimal: `@"a b"` is `__funk_sym_612062`, and
  `@""` is `__funk_sym_`. No word symbol starts with `_`, so the mapping
  is one-to-one, and it never gives a name that the toolchain or funk's
  runtime (`__funk_`) defines.

## Alternatives

- **Quoted symbols**, which GNU `as` allows, for every name. ELF names
  cannot hold NUL, and names with spaces or control characters confuse the
  tools that read symbol tables.
- **Hexadecimal for every name.** Simpler, but `@add3` would not be
  callable from C as `add3`.
- **Keep names that start with `_` too.** C++ mangled names (`_Z…`) would
  link as they are, but `_end` and `__bss_start` would silently become the
  linker's addresses, and calling them crashes.

## Consequences

- C can call a function whose name is a word starting with a letter, by
  that name, with `int8_t` to `int64_t` and `_Bool` arguments and result.
- A C++ frontend (M3) needs exact link names, such as `_ZN3foo3barEv`. That
  will take a way to state a function's link name, in a new ADR.
