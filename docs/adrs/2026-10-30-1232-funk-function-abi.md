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
- **Widths at the boundary.** An argument or result of `iN` has its value
  in the low `N` bits, and the bits above are unspecified
  (ADR-2026-10-30-1231): a callee reads only the low bits of each argument.
  An `i1` result is 0 or 1 in the whole of `%rax`, as C's `_Bool` is. What
  a caller extends before a call is #20's to decide.
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
