# f32 and f64 pass and return in SSE registers, as System V classifies them

Status: accepted
Tier: direction; area: x86-64-backend

## Context

The naive backend lowers `f32` and `f64` with SSE and reports every other
float format (ADR-2026-11-09-1549). A funk function follows the System V
AMD64 convention, so C can call it (ADR-2026-10-30-1232), and returns its
results as System V returns a structure with one member per result, each
aligned to 8 bytes (ADR-2026-11-03-0109). System V gives each eightbyte a
class: an integer is INTEGER and a `float` or `double` is SSE. INTEGER
eightbytes use `%rdi` to `%r9` and `%rax`, `%rdx`. SSE eightbytes use
`%xmm0` to `%xmm7` for arguments and `%xmm0`, `%xmm1` for results.

## Decision

- A value of `f32` or `f64` lives in one 8-byte slot or SSE register. Its
  low 32 or 64 bits are its bits, and the bits above are unspecified, as
  for an `iN` (ADR-2026-10-30-1231).
- An `f32` or `f64` argument takes the next free one of `%xmm0` to
  `%xmm7`, counted apart from the integer registers, or else the next
  eightbyte of the stack, in the order of the arguments. `abi::layout`
  is the one layout that the caller, the callee's prologue and the entry's
  stack figure read.
- Results keep one eightbyte per member. With one or two eightbytes, each
  INTEGER one comes back in the next of `%rax` and `%rdx`, and each SSE one
  in the next of `%xmm0` and `%xmm1`. So `f64, i64` comes back in `%xmm0`
  and `%rax`, as C returns `struct { double a; long b; }`. Three
  eightbytes or more go in the result area, as before.
- A float constant is written to its slot as an integer immediate of its
  bits. `fcmp` loads its operands with `movss` or `movsd` and compares them
  with `ucomiss` or `ucomisd`. `oeq` also needs the parity flag clear, and
  `une` accepts it set, since an unordered pair sets it.
- The built executable reads and prints an `f32` or `f64` as it reads and
  prints an `i32` or `i64`: the bits read as a signed integer
  (ADR-2026-11-11-1138).
- Every other float format is reported where its value is defined, as an
  unsupported integer width is.

## Consequences

- C calls a funk function with float parameters and results as it calls
  one declared with `float` and `double`, and a result structure whose
  members are aligned to 8 bytes.
- A register allocator must treat `%xmm0`, `%xmm1`, `%rax` and `%rcx` as
  clobbered by `fcmp`, and `%xmm0` to `%xmm7` as argument registers of a
  call.
