# Current decisions: the x86-64 backend

This page says what holds today for the x86-64 backend. It is the record: when
this page and an ADR disagree, the page wins, and the ADR is fixed or deleted
(ADR-2026-11-09-1610). It continues in
[x86-64-backend-abi.md](x86-64-backend-abi.md) (how a function looks from
outside), [x86-64-backend-executable.md](x86-64-backend-executable.md) (the
built executable and its stack) and
[x86-64-backend-lowering.md](x86-64-backend-lowering.md) (how ops lower).

## The crate

No target is built into the IR (ADR-2026-10-29-2016).

The backend is the library `crates/funk-x86-64`. It depends only on `funk-ir`,
which does not depend on it. The driver `funk` depends on both. A later target
is a crate of its own. Code that two targets share moves to a shared crate when
the second target arrives (ADR-2026-10-30-1228).

Its modules split by responsibility. `asm` writes assembly text. `width` says
how a value lives in a register. `abi` says how a function looks from outside.
`frame` lays out slots. `lower` lowers ops. `entry` writes an executable's
entry point. `tools` runs the assembler and the linker.

`lower/` has one file per op family. Each file maps op names to lowering
functions. A new family adds a file and one line in `lower/mod.rs`. An op with
no lowering is reported at its location, never skipped.

Diagnostics are `funk_ir::Diagnostic`s, located as the verifier locates them.
The backend uses no third-party crates (ADR-2026-10-30-1228).

## Assembly and linking

`funk build` needs GNU binutils on `PATH` on an x86-64 Linux host.
`scripts/ensure-hooks.sh` warns unless the host is x86-64 Linux and `as` and
`ld` are GNU binutils'. In CI, the `rust` and `cross` suite jobs install
binutils (ADR-2026-11-05-1408).

The backend writes GNU `as` assembly in AT&T syntax, as plain text. AT&T syntax
writes every register with `%`, so no symbol reads as a register.
`funk_x86_64::compile` returns this text, so a person or an agent can read what
the backend wrote.

Rejected: writing ELF directly, which needs an instruction encoder and an ELF
writer first and gives no readable output. The JIT will need an encoder, and
this text output will be its oracle. Also rejected: Intel syntax, in which a
function named `rax`, `byte` or `offset` would clash with a register or an
operator.

A build has two assembly files. One holds the module's functions and becomes
the object file. It may end with the backend's own routines, such as the
`i128` division helper
([x86-64-backend-lowering.md](x86-64-backend-lowering.md#division-at-i128)).
The other holds the executable's entry point and runtime. Both end with
`.note.GNU-stack`, so the stack is not executable.

`as --64` assembles each file. `ld -m elf_x86_64 -static` links the two objects
into a static executable with the entry point `__funk_start`. Both tools are
told the target, so neither a configured default nor `LDEMULATION` changes the
build. There is no C compiler. Each build starts two processes of `as` and one
of `ld`. Rejected: linking with libc through `cc`, which needs a C compiler
and makes the executable depend on it.

`funk build -o OUTPUT FILE` writes `OUTPUT.o` and `OUTPUT`. The intermediate
files go to a temporary directory, which funk removes.
[rust-ir-and-tools-funk.md](rust-ir-and-tools-funk.md#funk-build) says how the
outputs are moved into place.

A tool that prints is a tool that failed. If `as` or `ld` cannot run, exits
with an error or prints anything, such as a warning, the build fails with the
tool's words, a `tool-error`.

GNU binutils is not pinned, unlike Rust and Lean. CI takes it from its runner
image, and its log shows both versions; a machine uses its distribution's. So a
release that adds a warning, as 2.39 did for executable stacks, fails `funk
build` until the backend's output avoids it, and a local pass may not predict
CI's. Pinning (`apt-get install binutils=VERSION`) is the remedy if that
happens often.

### Linking with the host C library

A module whose object file references a symbol it does not define links with
the host's shared glibc instead, through `ld` alone: `ld -m elf_x86_64
--dynamic-linker /lib64/ld-linux-x86-64.so.2 -e __funk_start MODULE.o ENTRY.o
-lc`, with no C compiler and no `crt1.o`. That needs glibc's development files
(`libc.so`; Debian's and Ubuntu's `libc6-dev`), and the executable runs only
where that loader and glibc are. A symbol that no library defines is a
`tool-error` from `ld`. Any other module stays static, with no C library, and
the same entry file.

`funk build` decides from the object file's symbol table, not from a list that
lowering keeps, so it cannot miss a symbol that a lowering forgot. So the
module's object must define every routine of funk's own that it calls, as it
does the `i128` division and `fma` routines: a call to a routine of the entry
file would link with the C library for nothing.

The human ruled on 2026-11-11 (#274) that M1 links with the host's shared
glibc. A pinned static musl is filed as #295. How the runtime starts and exits
under glibc is on
[x86-64-backend-executable.md](x86-64-backend-executable.md#the-entry-file-and-its-runtime).

Rejected: static glibc, `libc.a`, which fails to link without glibc's start
files, and which glibc does not support without its start-up code. Also
rejected: always linking with the C library, which would make every program
need the loader and glibc's development files for no gain.

## Values and widths

A value of `iN`, with `N` at most 64, lives in one 64-bit register or slot. Its
low `N` bits are its bits, and the bits above are unspecified. This holds in
slots, in scratch registers, and for arguments and results. The one exception
is a returned `i1`, which the backend returns as 0 or 1 in all 64 bits, and on
which no caller relies (ADR-2026-10-30-1232).

`add`, `sub`, `mul`, `and`, `or`, `xor`, `trunc`, `select` and `freeze` work on
all 64 bits and extend nothing. Their result's low `N` bits depend only on
their operands' low `N` bits. So `add` at every width is one `addq`.

Other ops first extend what they read, by sign or by zero as the op reads it.
These are comparisons, `zext`, `sext`, the value of a right shift, and the
amount of every shift. Each op family's lowering says which operands it
extends and how. `width::extend` is the one place that knows the instructions.
A result printed or compared outside the backend, such as by the executable's
entry point, is extended first.

Division below `i128` extends nothing except at `i1`
([x86-64-backend-lowering.md](x86-64-backend-lowering.md#division)). A branch or
a `select` on an `i1` tests bit 0.

Rejected: keeping every value sign-extended to 64 bits. Comparisons would need
no extension, but every arithmetic op would need one after it, and values from
C would still need one on entry. Also rejected: sized instructions everywhere,
since `i1` has no register of its own and the rule for the bits above is still
needed at calls.

`width::check` accepts `i1`, `i8`, `i16`, `i32`, `i64`, `i128`, `f32` and
`f64`. Every other width or float format is reported as unsupported where its
value is defined: a parameter at its function's entry block, a result at its
op.

A value of `f32` or `f64` lives in one slot or SSE register. Its low 32 or 64
bits are its bits, and the bits above are unspecified, as for an `iN`. A float
constant is written to its slot as an integer immediate of its bits.

An `i128` is two eightbytes. Each half is 64 bits of the value, and no bit is
unspecified. `width::words` gives it two eightbytes
([x86-64-backend-lowering.md](x86-64-backend-lowering.md#lowering-i128)).

## Frames and slots

Register allocation is spill-everything: every value has its own slots below
`%rbp`. The parameters come first, then each block's arguments and each op's
results, in order. The baseline must be right by reading it, since every op
family builds on it. Rejected: a simple linear-scan allocator in M0, which
checks correctness, not speed; real allocation is M2's (docs/roadmap.md).

A value of at most 64 bits takes one 8-byte slot, and the `n`-th slot, from 1,
is at `-8n(%rbp)`. An `i128` takes two slots next to each other. Its low half
is at the lower address, so its 16 bytes are little-endian, as an `__int128` is
in memory.

Below the values' slots, a frame holds the address of its own result area when
its results go in memory. It also holds the address it passes to a call that
returns in memory. At its bottom is the area for its calls. That area is as
large as the largest any call needs, and is 16-byte aligned
([x86-64-backend-abi.md](x86-64-backend-abi.md#results)).

The prologue is `pushq %rbp; movq %rsp, %rbp`, then room for the frame. It
stores each parameter in its slot, from its register or from the caller's
stack. The epilogue is `leave; ret`. Every frame size is a multiple of 16, so
`%rsp` is 16-byte aligned wherever the function calls. A frame must fit 2 GiB,
the reach of a 32-bit displacement. A function with more values is reported as
unsupported.

An op loads its operands from their slots into scratch registers, computes, and
stores its results into their slots. No value stays in a register from one op
to the next, so lowering an op needs only its operands' and results' slots.
Scratch registers are caller-saved: `%rax`, `%rcx`, `%rdx` and the argument
registers. So a function saves only `%rbp`. The code is slow and large, since
every op reads and writes memory.

### Stack probes

A frame of less than a page is one `subq`; frames are multiples of 16, so such
a frame is at most 4080 bytes. A frame of 4096 bytes or more is probed.
`frame::prologue` moves `%rsp` down a page at a time and touches each page with
`orq $0, (%rsp)`. It counts pages in `%r11`, which carries no argument, then
subtracts the rest, less than a page. A frame of exactly 4096 bytes is one
probed page and no rest.

So every stack access is at most a page below one already made. A call's first
write below a frame, its return address or its padding and first stack
argument, is at most 16 bytes below the frame and at most a page below the last
access: the saved `%rbp` for a small frame, the lowest probe for a large one. A
frame too large for its stack faults at the stack's end, instead of jumping
past the guard region into other memory. `frame.rs` tests the prologue of a
4096-byte frame, and the call tests walk the assembly of calls from frames of
0 to 13, 500 to 530 and 1015 to 1030 values.

Rejected: no probes. Branches and calls break the downward order of writes, and
a call below an untouched frame can land past a guard page with no fault. Also
rejected: a probe routine, as `__chkstk` on Windows, which costs a call in every
large prologue and a symbol that C code linking the object file would have to
provide; and touching the frame's lowest slot before each call, which costs an
access at every call site rather than one probe in the prologue.

A funk function that C code calls runs on its caller's stack. A frame larger
than what is left there ends with `SIGSEGV`, as a C function's would. The
built executable runs each function on a stack of its own
([x86-64-backend-executable.md](x86-64-backend-executable.md#the-runs-stack)).

## Poison

Any value refines poison (ADR-2026-10-29-2008). The op `poison` gives a poison
result (ADR-2026-10-29-2006).

Native code has no poison value: every value is the bits in its slot. An op
whose source result is poison still stores some bits, and nothing relies on
which. `add`, `sub` and `mul` lower the same with any flags as without, and no
code tests a flag (ADR-2026-10-30-2248). So tests of a broken flag accept any
value of the type.

`freeze` is a copy. It loads its operand's slot and stores the bits in its own.
Only the `freeze` writes that slot, so every use sees the same bits. A `freeze`
that runs twice may give other bits each time (ADR-2026-10-30-2248). Tests of
`freeze` check that its uses agree, as `sub %f, %f` giving `0` does.

The op `poison` writes zero into each eightbyte of its result's slot, with
`movq $0`: one at `i1` to `i64`, two at `i128`
(`crates/funk-x86-64/src/lower/constant.rs`). A fixed value keeps native runs
reproducible: a `poison` that wrote nothing would give what the frame happened
to hold, and a failure against `fir-ref` must reproduce. Zero is a value of
every width with no masking. `freeze` uses no fixed value, since code cannot
know at run time whether a value is poison, while `poison` is poison where it
is written. A native run cannot tell `poison` from `const 0`.

The human ruled on 2026-11-03 (#122) that native code may lower `poison` to any
value. Rejected: writing nothing, which makes native results depend on chance;
and a recognisable pattern, which needs masking at `i1` and which no test can
tell from zero.

## What later work must keep

A register allocator must treat as clobbered:

- `%rax`, `%rcx` and `%rdx` by a division.
- `%rax`, `%rcx`, `%xmm0` and `%xmm1` by an `fcmp`.
- `%xmm0` by a float op of arithmetic, `%rax` by `fneg` and `fabs`, and every
  caller-saved register by an `fma`.
- `%rax` and `%rcx` by a branch.
- `%rax`, `%rcx` and `%rdx` by an `i128` op, and `%rsi` by a shift. It needs
  register pairs for `i128`.
- Every caller-saved register by an `i128` division.
- `%xmm0` to `%xmm7` as argument registers of a call.

Block arguments in registers need the same sequencing, and a scratch register
or an exchange for each cycle. x86-64-backend-lowering.md says how each op
lowers.

An optimizer that makes poison real must keep each `freeze` one value that every
use reads (ADR-2026-10-30-2248). The two halves of a frozen `i128` stay one
value.

It must read only bit 0 of every `i1`. No optimizer may turn a `select` into a
`cond_br` without freezing its condition first, or `select %c, %x, false` into
`and %c, %x` (`lean/Fir/Execution/PoisonUB.lean`). It may treat a `cond_br` on
poison as UB, as the spec does (ADR-2026-10-29-2006).

It must not make a division run where the source would not, such as by hoisting
it above the branch that tests its divisor: natively that adds a trap. It may
lower `poison` to anything, or fold it away.
