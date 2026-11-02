# A call between funk functions passes each argument as its slot holds it, and extends none

Status: accepted

## Context

[#20](https://github.com/pmatos/funk/issues/20) brings `call` to the
x86-64 backend, at `i1`, `i8`, `i16`, `i32` and `i64`. A value of `iN`
lives in the low `N` bits of its 64-bit slot, and the bits above are
unspecified (ADR-2026-10-30-1231): after `add`, an `i8` slot can hold 128
and an `i1` slot 2. A funk function reads only the low `N` bits of each
argument, and returns an `iN` result in the low `N` bits of `%rax`, an
`i1` as 0 or 1 in all of it (ADR-2026-10-30-1232).

C callees expect more. clang reads an `i8` or `i16` argument as extended
to 32 bits by the sign of its C type, and gcc and clang read a `_Bool`
argument as 0 or 1 in its low 8 bits. ADR-2026-10-30-1232 leaves to #20
what a funk caller extends, and asks for a sign- or zero-extension marker
on each narrow parameter before funk calls code that it did not compile,
since fir types carry no sign.

In M0 every callee is a function of the module: fir has no item that
declares a function defined elsewhere.

## Decision

- **No extension.** A call between funk functions passes each argument
  as its slot holds it, all 64 bits: the first six in their registers, the
  rest on the stack (ADR-2026-10-30-1232). It extends no argument, at any
  width.
- **The result as it comes.** The caller stores `%rax` in the result's
  slot as it is. Like every value, the result is then read only in its
  low `N` bits.
- **The marker waits for external callees.** The ticket that lets fir
  declare a function that funk did not compile defines the marker that
  ADR-2026-10-30-1232 asks for, and extends the narrow arguments of calls
  to such functions only. Until then no funk call reaches code that funk
  did not compile.

## Alternatives

- **Extend as C does**: `i8` and `i16` to 32 bits, `i1` to 0 or 1. fir
  types carry no sign, so a funk caller would have to guess one, and a
  funk callee ignores the extension anyway. It costs an instruction per
  narrow argument and buys nothing until external callees exist.
- **Extend every argument to 64 bits by sign.** A funk callee that reads
  `N` bits gains nothing from it either.

## Consequences

- A call loads each argument from its slot, calls, and stores the result:
  no extension instruction.
- C code may still call a funk function: it extends its arguments, and the
  funk function reads only their low bits.
- Native tests pass arguments whose slots hold bits above `N`, such as
  `127 + 1` at `i8`, whose slot holds 128, and check that each callee
  reads only the low `N` bits.
- The first call to code that funk did not compile must extend; this
  ADR's rule covers only calls between funk functions.
