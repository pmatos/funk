# Current decisions: the x86-64 backend, lowering ops

This page continues [x86-64-backend.md](x86-64-backend.md). It says what holds
today for how the naive backend lowers `select`, branches, block arguments,
`i128` values, the divisions and the floats. It is the record: when this page
and an ADR disagree, the page wins, and the ADR is fixed or deleted
(ADR-2026-11-09-1610). Each lowering here builds on spill-everything: an op
reads its operands from their slots and writes its results to theirs, and
native code holds no poison (ADR-2026-10-30-2248).

## `select`

Below `i128`, `select` is one `cmov`, with no branch. It loads its condition
into `%rcx` and its first value into `%rax`, and tests bit 0 with
`testb $1, %cl`. When the bit is clear, `cmovzq` moves in the second value from
its slot. It stores `%rax` as the result.

Nothing of the condition above bit 0 is read, so a condition whose slot holds
other bits, such as `true + true` at `i1` or a `trunc` to `i1`, chooses by its
value. Its tests run such conditions, which `testq %rcx, %rcx` would misread.
The chosen slot's 64 bits are copied, and its low `N` bits are the result.
`select` reads both slots whatever its condition, which costs one load and
never faults. Where the source gives poison, from the condition or from the
chosen value, the result is the bits of one of the two slots, which refines
poison. A poison value that is not chosen never reaches the result.

Rejected: a branch on bit 0, which needs two labels and a jump in every
`select`, where a mispredicted jump costs more than a `cmov`; and masks of bit
0 with `and`, `andn` and `or`, which are longer, and `andn` needs BMI1.

## Branches

A function's blocks are laid out in the order of its body, so assembly reads
alongside the fir text. Each block is at the label `.Lb` followed by the
function's index in the module, `_` and the block's label, such as
`.Lb0_loop`. A block label is letters, digits, `_` and `.`, so each is a valid
GNU `as` symbol, and the index ends at the first `_`, so no two functions'
labels collide. Every block of a valid function is reachable
(ADR-2026-10-30-0817), so the backend sees no dead code.

`br` copies its block arguments, then jumps with `jmp` to its block, unless that
block comes next. `cond_br` loads its condition into `%rax` and tests bit 0 with
`testb $1, %al`, before any copy. A `jnz` to the first successor or `jz` to the
second then goes to one edge, and the code of the other edge follows it. An
edge with nothing to copy has no code of its own, so the jump goes straight to
its block. Otherwise the jumped-to edge's code goes after the other's, at a
local label `.Lc` followed by the function's index, `_` and a count. An edge's
code is its copies and a `jmp` to its block. Only the code that ends the branch
may leave the `jmp` out, when its block comes next, so the edges are ordered to
let that edge end it. A `cond_br` whose two edges both copy costs one local
label and one extra jump.

A branch on poison is immediate UB (ADR-2026-10-29-2006), and goes one way or
the other. `cond_br` loads its condition into `%rax`, a copy goes through
`%rax`, and a cycle of copies through `%rcx`, so a branch may clobber both.

Rejected: always jumping, which puts a `jmp` to the next instruction in every
loop body and fall-through; and reordering blocks, such as a loop's body after
its header, which improves the code, not its correctness.

`unreachable` is `ud2`. A run that reaches it is UB, so any code would do, and
`ud2` stops the run instead of falling into the next block. This is a choice of
the naive backend, recorded in the doc comment of `lower/control.rs`.

## Block arguments

A branch copies the values it passes into its block's arguments as one
parallel move: `br ^loop(%b, %a)` swaps, `br ^loop(%b, %c, %a)` rotates, and
`br ^loop(%a, %a)` passes one value to two arguments. The arguments of a block
are distinct values, so no two copies of one branch write the same slot.

`moves.rs` turns an edge's copies into steps. It drops a copy from a slot to
itself. Then, while copies remain, it does one whose destination no remaining
copy reads. When none is left, the remaining copies form cycles. The first
remaining destination is saved in `%rcx`, and the copies that read that slot
read `%rcx` instead, which opens its cycle into a chain.

A copy is `movq` from its slot into `%rax` and from `%rax` into its
destination. Saving is `movq` from the slot into `%rcx`, and a copy from the
register is one `movq` from `%rcx`. Every copy moves all 64 bits, so a value's
low `N` bits arrive as they were. A branch makes one copy per argument whose
slot is not its value's, and one save per cycle. On a `cond_br` the copies come
after the test. A unit test runs random parallel moves against copies done at
once, and the native tests swap, rotate and fan out arguments round loops.

Rejected: pushing every value and popping each into its argument, which costs
two stack accesses per argument and moves `%rsp` mid-function; and a temporary
slot per argument, which doubles the copies and grows the frame.

## Lowering `i128`

`i128` is in the M0 backend through register pairs, with division through a
runtime helper (ADR-2026-10-29-2007). An op at `i128` loads each operand's low
half into `%rax` and its high half into `%rdx`. It computes and stores both
halves. `const` writes two immediates. `add` and `sub` carry between the halves
with `adcq` and `sbbq`. `mul` is `mulq` of the low halves. The low 64 bits of
the two cross products, each by `imulq` in `%rcx`, are added into the high
half. Their flags lower as no flags do. `and`, `or` and `xor` apply to each
half.

A shift reads the low half of its amount into `%rcx`. `shldq` or `shrdq` by
`%cl` moves bits between the halves, and `shlq`, `shrq` or `sarq` shifts the
half they fill; x86 masks those counts to 6 bits. `testb $64, %cl` and two
`cmovneq` then move the halves one place further for an amount from 64 to 127,
filling with zero, or with the sign for `ashr`, from `%rsi`. No code branches
on the amount. An amount of 128 or more gives poison, and gets whatever this
sequence gives for its low 7 bits.

`icmp eq` and `ne` `xorq` each half with the other operand's and `orq` the two.
Other predicates are `cmpq` of the low halves and `sbbq` of the high ones, then
`setl`, `setge`, `setb` or `setae`, with the operands swapped for `sgt`, `sle`,
`ugt` and `ule`. That borrow chain sets the carry, sign and overflow of the
128-bit subtraction, but not its zero flag. `select` tests bit 0 and uses one
`cmovzq` per half.

`zext` and `sext` extend the operand to 64 bits with `width::extend` and fill
the high half with zero, or with `sarq $63` of the low one. `trunc` copies the
low half. A branch passes an `i128` as two copies of its parallel move, so a
swap of two `i128`s is two cycles. `ret` returns an `i128` in `%rdx:%rax`.

Poison is not tracked per half. `freeze` copies both halves into its own two
slots, which no other op writes, so every use of a frozen value sees the same
128 bits. `crates/funk-x86-64/tests/pair.rs` pins each sequence, and
`crates/funk/tests/i128_ops.rs` runs each op natively against Rust's `i128` and
`u128` arithmetic.

Rejected: the high half at the lower address, which would swap the halves of an
`__int128` that C passes on the stack; SSE registers, which have no 128-bit
add, multiply, shift or compare, and no carry; a branch on bit 6 of a shift
amount, which costs two labels and a jump in every shift; and a poison bit per
value or per half, which nothing reads.

## Division

A zero or poison divisor is immediate UB in the source. So is `sdiv` or `srem`
by `-1` of the signed minimum or of poison (ADR-2026-10-29-2006). The human
ruled the poison dividend by `-1` UB on 2026-10-30, so that a backend needs no
guard.

Below `i128`, `sdiv` and `srem` are one `idiv`, and `udiv` and `urem` one `div`,
of size `b`, `w`, `l` or `q` at `i8`, `i16`, `i32` and `i64`. The dividend goes
in `%rax` and the divisor in `%rcx`. The instruction reads only their low `N`
bits, so neither is extended to 64 bits. The dividend is widened into the high
half that the instruction also reads: `cbtw`, `cwtd`, `cltd` or `cqto` for the
signed ops, `movzbl %al, %eax` or `xorl %edx, %edx` for the unsigned ones. The
quotient is in `%rax`. The remainder is in `%rdx`, or in `%ah` at `i8`, which
`movb %ah, %al` moves down.

`i1` divides as `i8`, after both operands are extended to 64 bits with
`width::extend`. Its defined cases are `false` by `true` for `sdiv` and `srem`,
and either value by `true` for `udiv` and `urem`.

No code tests the divisor or the dividend. A zero divisor traps, and so does the
signed minimum by `-1` at `i8` to `i64`. At `i1`, `true` by `true` gives some
value and does not trap, which UB allows too. `sdiv exact` and `udiv exact`
lower as `sdiv` and `udiv`: where `exact` is broken the quotient refines
poison. Native tests run only inputs whose result is not UB.

Rejected: extending both operands and using `idivq` or `divq` at every width,
since below `i64` the signed minimum by `-1` would no longer trap, and the
source's UB would go unseen where the hardware shows it; and a guard that tests
the divisor, which costs a test and a branch on every division for inputs on
which the spec allows anything.

## Division at `i128`

x86-64 has no instruction that divides 128 bits by 128. At `i128`, each op
calls one of `__funk_rt_sdiv128`, `__funk_rt_udiv128`, `__funk_rt_srem128` or
`__funk_rt_urem128`, which share `__funk_rt_udivmod128` and
`__funk_rt_magnitudes`. These are hand-written assembly in
`crates/funk-x86-64/src/lower/div128.s`, held as text with `include_str!`.
`lower::module` appends that file once to a module's assembly, after its
functions, when a function of it divides at `i128`, and any other module's
assembly is as before. So `OUTPUT.o` stands alone: C code that links it needs
no runtime library.

No routine is `.globl`, so each is a local symbol of the object file that holds
it, and two such objects link into one C program. No fir function's symbol
starts with `__funk_rt_`: a word symbol starts with a letter, and every other
starts with `__funk_sym_`. So a function named `@__funk_rt_sdiv128` gets a
`__funk_sym_` symbol, as the corpus module `div-symbol-i128` checks. The
routines' labels start with `.Lrt_div128_`, which no block label (`.Lb`) or
other local label (`.Lc`) does.

Each routine is a System V function `__int128 f(__int128 a, __int128 b)`: `a`
in `%rdi` and `%rsi`, `b` in `%rdx` and `%rcx`, low half first, and the result
in `%rax` and `%rdx`. They use only `%rax`, `%rcx`, `%rdx`, `%rsi`, `%rdi` and
`%r8` to `%r11`, and leave `%rsp` as they found it. The caller keeps nothing in
a register across the op, so nothing is saved around the call.

`__funk_rt_udivmod128` gives the unsigned quotient and remainder. A `b` below
`2^64` takes two `divq`: `a`'s high half by `b`, then that remainder and `a`'s
low half. Otherwise restoring division takes the 64 bits of `a`'s low half, one
a step, into a remainder that starts as `a`'s high half. The signed routines
divide the magnitudes and negate the quotient when the signs differ, and the
remainder when `a` is negative. A zero divisor traps in the first `divq`, as at
`i64`, and the signed minimum by `-1` gives some value. There is no guard.
`exact` calls the routines of `sdiv` and `udiv`.

A routine uses at most 24 bytes below its caller's `%rsp`: its return address,
the sign that `__funk_rt_sdiv128` and `__funk_rt_srem128` push, and their call
of a shared routine. The stack figure counts it
([x86-64-backend-executable.md](x86-64-backend-executable.md#the-figure)).
`crates/funk-x86-64/tests/div128.rs` pins the call and where the helper goes.

Rejected: the helper in the entry's runtime, or in a separate object or
archive, which leaves `OUTPUT.o` an undefined symbol that C code would have to
provide; libgcc's `__divti3` and kin, since funk links no libgcc; global
symbols, which collide when a C program links two such objects; the helper in
every module, or inline at each division; Hacker's Delight's estimate for a
large `b`, which is faster but easy to get subtly wrong in hand-written
assembly; and a convention of its own, where System V is the one the backend's
other calls follow.

## Float comparison

`fcmp` loads its operands with `movss` or `movsd` into `%xmm0` and `%xmm1`,
compares them with `ucomiss` or `ucomisd`, and reads the flags with one
`setCC`, or two for `oeq` and `une`. `oeq` also needs the parity flag clear, and
`une` accepts it set, since an unordered pair sets it.

## Float arithmetic

The backend lowers the float arithmetic at `f32` and `f64` with SSE2, which every
x86-64 has, and the remainders with the x87 unit, which every x86-64 has too. `fadd`, `fsub`, `fmul`, `fdiv` and `sqrt` are one instruction
each, `addss`, `subss`, `mulss`, `divss`, `sqrtss` or their `sd` forms, on
`%xmm0` and the second operand's slot. MXCSR keeps its default mode, round to
nearest even. Nothing sets its flush-to-zero or denormals-are-zero bits, so
subnormals are honoured. `fneg` and `fabs` flip or clear the sign bit in `%rax`
with `btcq` or `btrq`, which is IEEE 754's negate and abs, also on a NaN, and
refines fir's any NaN (ADR-2026-11-09-1549). A NaN result is whatever the
instruction or routine gives.

SSE2 has no fused multiply-add, and FMA3 is not in every x86-64. So `fma` loads
its operands into `%xmm0` to `%xmm2` and calls `__funk_rt_fmaf` or
`__funk_rt_fma`, hand-written in `crates/funk-x86-64/src/lower/fma.s`, which
`lower::module` appends once as it appends `div128.s`. Each is a System V
function of three floats that uses only caller-saved registers and 16 bytes of
stack, within the 24 bytes that the stack figure counts for a helper.

At `f32` the product is exact in `f64`. The routine rounds the sum to odd in
`f64`, toward zero with the last bit set when it was inexact, and then to
nearest even in `f32`. Rounding to odd with two more bits rounds once (Boldo
and Melquiond, 2008). MXCSR is restored after. At `f64` it computes
`a * b + c` exactly in 128-bit integers and rounds once, subnormals and
overflow included. NaN and infinite operands, and zeros, take SSE's
`a * b + c` or `a * b`, which is exact or correctly signed there.
`crates/funk/tests/float_arith.rs` checks every op against the host's IEEE 754
arithmetic.

Rejected: FMA3's `vfmadd`, since a program that uses it fails on an x86-64
without FMA3, and the default stays baseline x86-64 (the human ruled on
2026-11-12 that CPU extensions come in through a `--cpu` flag in M2; see
[the roadmap](../roadmap.md));
`fma` from the C library, since most modules link none; and double-double
arithmetic at `f64`, which loses exactness near overflow and among subnormals.

### The remainders

SSE has no remainder. So `frem` and `fmod` load their operands into `%xmm0` and
`%xmm1` and call `__funk_rt_fremf`, `__funk_rt_frem`, `__funk_rt_fmodf` or
`__funk_rt_fmod`, hand-written in `crates/funk-x86-64/src/lower/frem.s`, which
`lower::module` appends once as it appends `fma.s` (#310). Each routine moves
its operands through one pushed word onto the x87 stack and runs `fprem1`, IEEE
754's remainder with the quotient rounded to nearest even, for `frem`, or
`fprem`, C's `fmod` with the quotient truncated, for `fmod`. Each reduces the
exponent by at most 63 bits at a time and sets C2 while it is partial, so the
routine loops until C2 is clear: about 34 times for the largest `f64` by the
smallest subnormal. Both are exact whatever the x87 precision control says, and
the result is exact in the format, so the store to `f32` or `f64` is exact.
They give a NaN on `y = 0` or an infinite `x`, `x` itself on an infinite `y`,
and a zero with `x`'s sign, as the spec does. A routine uses `%rax`, `%xmm0`,
`%xmm1` and the x87 stack, which it leaves empty, and 16 bytes of stack.
`crates/funk/tests/float_arith.rs` checks both against the host's arithmetic on
the hard values and on random operands, operands far apart and quotient ties
among them.

Rejected: `fmod` and `remainder` from the C library, since most modules link
none; and a routine on the integer unit that shifts and subtracts the
mantissas, which is longer, slower on far-apart operands, and needs its own
proof of the rounding of the quotient, where `fprem1` is IEEE 754's own.
