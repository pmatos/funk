# A funk function returns its results as System V returns a structure of one eightbyte per result

Status: accepted

## Context

fir functions and calls have any number of results, none included
(ADR-2026-10-30-0816). ADR-2026-10-30-1232 makes a funk function a System V
AMD64 function, callable from C, and returns no value or one value in
`%rax`; it leaves more to [#31](https://github.com/pmatos/funk/issues/31).

- System V returns integers in `%rax`, then `%rdx`. A structure of more
  than two eightbytes goes in memory: the caller passes the address of
  space for it in `%rdi`, as a hidden first argument, so the other
  arguments move along by one. The callee writes the structure there and
  returns the address in `%rax`. One `__int128` comes back in `%rdx:%rax`,
  the low half in `%rax`; in a structure it is aligned to 16 bytes.
- A value of `iN` lives in the low `N` bits of its 64-bit slot, and every
  value has a slot of its own (ADR-2026-10-30-1231, ADR-2026-10-30-1230). A
  call extends no argument and stores its result as it comes
  (ADR-2026-11-02-1021). One emitter places a call's arguments
  (ADR-2026-11-02-1428), and the executable's stack figure counts what each
  call pushes (ADR-2026-11-02-1132).
- [#21](https://github.com/pmatos/funk/issues/21) brings `i128` through
  register pairs, and either ticket may land first.
- fir has no memory in M0. A result area is backend stack space, like a
  slot.

## Decision

- **The results are a structure.** A function returns its results as
  System V returns a C structure with one member per result, in order,
  each aligned to 8 bytes. A result of at most 64 bits takes one eightbyte
  of its own. An `i128` takes two, at an offset that is a multiple of 16,
  its low half first. To C, results `T1, ..., Tn` are
  `struct { _Alignas(8) C1 r1; ...; _Alignas(8) Cn rn; }`, where `Ck` is
  `_Bool`, `intN_t`, `uintN_t` or `__int128` as the result's width says.
- **Two eightbytes come back in registers.** No result returns nothing. When
  the results take one or two eightbytes, the first is in `%rax` and the
  second in `%rdx`: one result in `%rax`, two in `%rax` and `%rdx`, and one
  `i128` in `%rdx:%rax`.
- **More go in an area that the caller provides.** When the results take
  three eightbytes or more, every one of them goes in memory. The caller
  passes the address of a result area as the call's first argument, in
  `%rdi`; the call's own arguments follow it, so its fifth goes in `%r9`
  and its sixth on the stack. Each result is at the next offset that is a
  multiple of its alignment, and the area's size is rounded up to 16
  bytes. The callee keeps the address in a slot of its frame. Its `ret`
  writes every result to the area and returns the address in `%rax`.
- **The area is in the caller's frame.** Below its values' slots, a frame
  holds one slot for the address of its own result area, when its results
  go in memory, and one for the address it passes to a call, when a call
  of it returns in memory. At its bottom it holds the area for its calls:
  as large as the largest that any of them needs, and 16-byte aligned,
  since `%rbp` and every frame size are multiples of 16. Each such call
  reuses it, and the caller copies each result into its slot right after
  the call. The executable's entry wrapper (ADR-2026-10-30-1233) is a
  caller like any other.
- **Narrow results.** A result of `iN` is in the low `N` bits of its
  eightbyte, and the bits above are unspecified, as in a slot. An `i1`
  result is 0 or 1 in all 64 bits, in a register or in the area, as
  ADR-2026-10-30-1232 returns one `i1` today, so C reads a `_Bool` member
  as it expects. The caller stores each eightbyte in its result's slot as
  it comes, with no extension, as ADR-2026-11-02-1021 stores `%rax`.
- **One place.** `crates/funk-x86-64/src/abi/results.rs` lays the results
  out and emits both sides: what `ret` gives and what a caller receives.
  The lowering of `ret` and `call` and the entry wrapper all use it. The
  area's address goes through `abi::call` as the first argument slot, and
  the stack figure counts it among the call's arguments.

## Alternatives

- **More return registers before memory**, as Swift returns four. Fewer
  stores, but C cannot call a function of three or four results, and the
  backend would keep two conventions. Speed is M1's concern.
- **A funk-only area**, with its address in a register that carries no
  argument. No argument moves, but C cannot call a function with more than
  two results, and a C frontend that returns a structure would need a
  second convention.
- **Pack narrow results as C lays out their natural types**, two `i8` in
  one eightbyte. Every `ret` and call would pack and unpack, and whether
  results fit in registers would depend on their widths.
- **The call's result slots as the area.** No copy, but slots run down from
  `%rbp` while a structure runs up, and an `i128` needs 16-byte alignment.
- **The area below the frame at each call**, as stack arguments are. A large
  area would need probing before the call (ADR-2026-11-02-1102), and the
  cleanup that ADR-2026-11-02-1428 runs right after the call would have to
  wait until the results are read.

## Consequences

- C can call every funk function whose symbol is its name, at any number of
  results, as a function that returns the structure above.
- Functions and calls of no result or one result compile as before.
- A call whose results go in memory has one argument register fewer.
- With #21, an `i128` result alone comes back in `%rdx:%rax`; next to any
  other result it goes in memory, in two eightbytes, 16-byte aligned. The
  layout in `abi/results.rs` places it so already; the lowering moves its
  two halves when #21 lets the backend hold an `i128`.
- ADR-2026-10-30-1232's results rule and ADR-2026-10-30-1230's frame size
  are refined. The executable's command line and output do not change: the
  wrapper prints every result, in order, as ADR-2026-10-30-1233 already
  says.
