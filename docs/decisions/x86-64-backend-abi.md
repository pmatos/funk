# Current decisions: the x86-64 backend, the function ABI

This page continues [x86-64-backend.md](x86-64-backend.md). It says what holds
today for how a funk function looks from outside: its convention, its symbol,
and how it takes arguments and returns results. It is the record: when this
page and an ADR disagree, the page wins, and the ADR is fixed or deleted
(ADR-2026-11-09-1610).

## Convention and symbols

A funk function is a System V AMD64 function and a global function symbol
(`.globl`, `@function`), so C can call it. `%rsp` is 16-byte aligned at each
call. `%rbx`, `%rbp` and `%r12` to `%r15` are callee-saved
(ADR-2026-10-30-1232).

A fir name that is a word starting with a letter is its own symbol. A word
holds letters, digits, `_` and `.`. Every other name, including every name that
starts with `_`, is `__funk_sym_` followed by its UTF-8 bytes in lower-case
hexadecimal. So `@"a b"` is `__funk_sym_612062`, and `@""` is `__funk_sym_`.
The mapping is one-to-one, and never gives a name that the toolchain, such as
`ld`'s `_end` and `__bss_start`, or funk's runtime (`__funk_`) defines
(ADR-2026-10-30-1232).

C can call a function whose name is a word starting with a letter, by that
name. The C and C++ frontend (M4) will need exact link names, such as
`_ZN3foo3barEv`. How a function states its link name is then decided by
editing ADR-2026-10-30-1232 in place.

Rejected: quoted symbols for every name, since ELF names cannot hold NUL and
names with spaces or control characters confuse the tools that read symbol
tables; hexadecimal for every name, since `@add3` would not be callable from C
as `add3`; and keeping names that start with `_`, since `_end` and
`__bss_start` would silently become the linker's addresses
(ADR-2026-10-30-1232).

## Arguments

Integer arguments go in `%rdi`, `%rsi`, `%rdx`, `%rcx`, `%r8` and `%r9`, then on
the stack, the first stack eightbyte at `8(%rsp)` on entry. A funk function
reads only the low `N` bits of each `iN` argument (ADR-2026-10-30-1232).

`abi::layout` (`crates/funk-x86-64/src/abi/layout.rs`) maps a call's arguments,
each of one or two eightbytes, to their places by System V's rules. An `i128`
is two eightbytes of class INTEGER. It goes in two registers when two are free.
Otherwise all of it goes on the stack, aligned to 16 bytes, and a register left
free goes to a later argument. The stack area is padded to a multiple of 16. So
a call with `i128` arguments may leave a register unused and a hole on the
stack. Its tests pin the layouts that gcc 16 and clang give these C prototypes,
with `long` for one eightbyte:

- `g1(long a, b, c, d, e, __int128 x, long y)`: `x` at 0 and 8 above `%rsp` at
  the call, and `y` in `%r9`.
- `g2(long a, b, c, d, e, f, s, __int128 x, long t)`: `s` at 0, a hole, `x` at
  16, `t` at 32, and 48 bytes in all.
- `g3(__int128 a, b, c, d, long e)`: `a`, `b` and `c` in register pairs, `d` at
  0, `e` at 16.
- `g4(long a, __int128 b, c, d)`: `d` at 0, and `%r9` unused.

The caller, the callee's prologue, the entry wrapper and the executable's stack
figure all read this one layout, so they cannot disagree. The caller pushes the
stack area from the top down, one `pushq` per eightbyte, high half before low
half, and a hole as `subq $8, %rsp`; then it loads the registers. The callee
stores each eightbyte from its register, or from `16 + offset(%rbp)` for one at
`offset` above `%rsp` at the call.

Rejected: splitting an `i128` between `%r9` and the stack, or leaving it
unaligned on the stack, which is not System V, so a C caller would disagree;
and passing an `i128` by reference to a copy, which costs a copy per call and
is not how C calls a function that takes an `__int128`.

## Floats in SSE registers

The backend follows System V's classes for `f32` and `f64`: an `f32` or `f64`
eightbyte is of class SSE. An `f32` or `f64` argument takes the next of `%xmm0`
to `%xmm7`, counted apart from the integer registers, or else the next
eightbyte of the stack, in the order of the arguments. `abi::layout` places it
with the others.

Among the results, which keep one eightbyte per member, an SSE eightbyte comes
back in the next of `%xmm0` and `%xmm1`, and an INTEGER one in the next of
`%rax` and `%rdx`. So `f64, i64` comes back in `%xmm0` and `%rax`, as C returns
`struct { double a; long b; }`. Three eightbytes or more go in the result area,
as below. So C calls a funk function with float parameters and results as it
calls one declared with `float` and `double`.

## Results

fir functions and calls have any number of results (ADR-2026-10-29-2008). A
funk function returns them as System V returns a C structure with one member
per result, in order (ADR-2026-10-30-1232). C can call every funk function
whose symbol is its name as such a function.

Each member is aligned to 8 bytes, or to 16 for an `i128`. A result of at most
64 bits takes one eightbyte of its own. An `i128` takes two, at an offset that
is a multiple of 16, its low half first. To C, results `T1, ..., Tn` are
`struct { M1; ...; Mn; }`. For a result of at most 64 bits, `Mk` is
`_Alignas(8) Ck rk`, where `Ck` is `_Bool`, `intN_t` or `uintN_t` as its width
says. For an `i128`, `Mk` is `__int128 rk`, with no `_Alignas`, since C forbids
`_Alignas` to lower an alignment.

A function with no results returns nothing. One or two eightbytes come back in
registers, the first in `%rax` and the second in `%rdx`. So one `i128` comes
back in `%rdx:%rax`, and next to any other result an `i128` goes in memory.

Three eightbytes or more all go in memory. The caller passes the address of a
result area as the first argument, in `%rdi`, as C passes the address of a
structure that it returns in memory. The call's own arguments follow it, so its
fifth goes in `%r9`, and an `i128` argument looks for its pair from `%rsi` on.
The layout reads the address first everywhere: the prologue and the stack
figure build their list with `abi::passed`, and `lower/call.rs` and the entry
wrapper pass it as their first `Arg`.

Each result is at the next offset that is a multiple of its alignment, and the
area's size is rounded up to 16 bytes. The callee keeps the address in a slot
of its frame. Its `ret` writes every result to the area and returns the address
in `%rax`. The area is in the caller's frame, at its bottom
([x86-64-backend.md](x86-64-backend.md#frames-and-slots)), and each call
reuses it. The caller copies each result into its slot right after the call.
The entry wrapper is a caller like any other.

An `iN` result is in the low `N` bits of its eightbyte, and the bits above are
unspecified. The caller stores each eightbyte as it comes, with no extension.
`crates/funk-x86-64/src/abi/results.rs` lays out and emits both sides: what
`ret` gives and what a caller receives. The lowering of `ret` and `call` and the
entry wrapper all use it.

Rejected: more return registers before memory, as Swift returns four, and a
funk-only result area with its address in a register that carries no argument.
Either way C could not call a function of three or more results, and the
backend would keep two conventions. Also rejected: packing narrow results as C
lays out their natural types, since every `ret` and call would pack and unpack;
the call's result slots as the area, since slots run down from `%rbp` while a
structure runs up; and an area below the frame at each call, which would need
probing and would delay the call's cleanup (ADR-2026-10-30-1232).

## The unmarked `i1` result

The backend returns an `i1` result as 0 or 1 in all 64 bits, in `%rax` or in
its eightbyte among several results, so C reads a `_Bool` member as it expects.
No caller, funk's own code included, may rely on the bits above bit 0 of an
unmarked `i1` result. A caller that needs a C `_Bool` relies on the `zext`
marker (ADR-2026-11-09-1547). The runtime reads an `i1` result by bit 0
(ADR-2026-10-30-1232).

The human ruled this on #251 on 2026-11-11, choosing option A: an unmarked
`i1` promises nothing, and the backend may keep returning 0 or 1. So a later
backend or pass may return an unmarked `i1` with any upper bits. Rejected:
keeping the guarantee, which would hold every unmarked `i1` result to more than
ADR-2026-11-09-1547 promises.

## Calls between funk functions

A call between funk functions passes each argument as its slot holds it, all
64 bits. It extends no argument, at any width. The caller stores `%rax` in the
result's slot as it is, read only in its low `N` bits like every value. Native
tests pass arguments whose slots hold bits above `N`, such as `127 + 1` at
`i8`, and check that each callee reads only the low `N` bits. M1's optional
markers let a signature ask for an extension (ADR-2026-11-09-1547).

Rejected: extending as C does, `i8` and `i16` to 32 bits and `i1` to 0 or 1.
fir types carry no sign, so a funk caller would have to guess one, and a funk
callee ignores the extension anyway. Also rejected: extending every argument to
64 bits by sign, from which a funk callee gains nothing either.

## One emitter for funk calls

`abi::call` is the one emitter of outgoing funk calls. It emits a complete call
from a fir function name and argument slots in parameter order. It owns
register selection, reverse pushes, padding, symbol spelling and cleanup, and
moves each slot's bits without extension. Fir call lowering and the entry
wrapper both use it, and both restore outgoing space right after the call.
Cleanup leaves the result in `%rax` and restores alignment.

The emitter returns its peak outgoing argument bytes, padding included and the
return address excluded. The entry's stack figure reads them, and owns frame
sizes, return addresses, runtime space and rounding. The emitter checks that
cleanup fits a signed 32-bit immediate before it writes assembly. Its callers
keep width checks, located diagnostics and result storage or printing. Fir call
lowering collects argument slots before it emits, so a failed lookup cannot
leave a call half written. The emitter is internal to the x86-64 crate.

The wrapper's calls of the runtime and calls of the `i128` division and `fma`
routines are plain `call`s, outside `abi::call`.

Rejected: a separate call layout with a cleanup choice, which gives callers a
lifetime rule and an argument-count invariant; and a callback for result
handling, which adds an ordering rule that neither caller needs.

## Code that funk did not compile

C callees expect more of a narrow argument than a funk callee does. clang reads
an `i8` or `i16` argument as extended to 32 bits by the sign of its C type, and
gcc and clang read a `_Bool` argument as 0 or 1 in its low 8 bits. A slot after
`add` can hold neither: 127 + 1 at `i8` leaves 128, and `true + true` at `i1`
leaves 2 (ADR-2026-10-30-1232).

fir types carry no sign, so an extension needs a marker. ADR-2026-11-09-1547
defines it, with M1's external declarations; semantics-m1-design.md has the
design. An integer parameter or result narrower than 32 bits may carry `sext`
or `zext`. The marker is optional, and frontends set it to match the C ABI. The
backend extends a marked argument at the call and a marked result at the
return, and nothing unmarked. An `i1` marked `zext` is a C `_Bool`. With no
marker, neither side may rely on the upper bits.

C defines only bits 0 to 7 of a `_Bool` result: bit 0 is the value, and bits 1
to 7 are zero. So code that calls a C function may rely only on bit 0 of an
unmarked `i1` result, and a caller that needs a C `_Bool`, 0 or 1 in `%al`,
relies on the `zext` marker.
