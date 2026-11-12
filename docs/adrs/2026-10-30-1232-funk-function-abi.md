# A funk function is a System V AMD64 function, with a symbol made from its fir name

Status: accepted
Tier: direction; area: x86-64-backend

## Decision

- **System V AMD64.** Every fir function is a global function symbol and a
  System V AMD64 function, so C can call it. It reads only the low `N` bits of
  each `iN` argument. Each argument goes where System V's classes put it,
  `i128` and floats included.
- **Results are a structure.** A function returns its results as System V
  returns a C structure with one member per result, in order, each aligned to
  8 bytes, or to 16 for an `i128`. With no results it returns nothing. One or
  two eightbytes come back in registers. Three or more go in an area whose
  address the caller passes as the first argument.
- **Narrow results.** An `iN` result is in the low `N` bits of its eightbyte.
  The backend may return an unmarked `i1` as 0 or 1 in all 64 bits, but no
  caller, funk's own code included, relies on any bit above bit 0. A caller
  that needs a C `_Bool` relies on the `zext` marker of ADR-2026-11-09-1547.
  The human ruled this on #251 on 2026-11-11.
- **Code that funk did not compile** expects narrow arguments extended as their
  C types say. fir types carry no sign, so such calls extend only what the
  optional markers of ADR-2026-11-09-1547 ask for.
- **Symbols.** A fir name that is a word starting with a letter (letters,
  digits, `_` and `.`) is its own symbol. Every other name, including every
  name that starts with `_`, is `__funk_sym_` followed by its UTF-8 bytes in
  lower-case hexadecimal: `@"a b"` is `__funk_sym_612062`. The mapping is
  one-to-one, and never gives a name that the toolchain or funk's runtime
  (`__funk_`) defines.
- **Link names.** The C and C++ frontend (M4) needs exact link names, such as
  `_ZN3foo3barEv`. How a function states one is decided by editing this ADR.

[x86-64-backend-abi.md](../decisions/x86-64-backend-abi.md) has the layouts.

## Why

C code calls funk functions, and a C frontend must call C, so one convention
serves both. Any string is a fir symbol (ADR-2026-10-29-2012), but an
assembler and an ELF symbol table cannot take every string, and `ld` defines
`_end` and `__bss_start` itself. A promise about an unmarked `i1` beyond what
ADR-2026-11-09-1547 gives would bind every later backend to an extension.

## Rejected alternatives

- **More return registers before memory**, as Swift returns four, or a
  funk-only result area. C could not call a function of three or more results,
  and the backend would keep two conventions.
- **Narrow results packed as C lays out their types.** Every `ret` and call
  would pack and unpack.
- **Quoted symbols for every name.** ELF names cannot hold NUL, and spaces
  confuse the tools.
- **Hexadecimal for every name.** `@add3` would not be callable as `add3`.
- **Keeping names that start with `_`.** `_end` would silently become the
  linker's address.
- **Keeping the 0-or-1 guarantee for an unmarked `i1`.** The human chose
  against it on #251.
