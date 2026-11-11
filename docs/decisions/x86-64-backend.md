# Current decisions: the x86-64 backend

This page says what holds today for the x86-64 backend. It only summarizes
the ADRs it cites (ADR-2026-11-09-1610). When this page and an ADR disagree,
the page has a bug.

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

`funk build` needs GNU binutils on `PATH` on an x86-64 Linux host. In CI, the
`rust` and `cross` suite jobs install binutils (ADR-2026-11-05-1408).

The backend writes GNU `as` assembly in AT&T syntax, as plain text. AT&T syntax
writes every register with `%`, so no symbol reads as a register.
`funk_x86_64::compile` returns this text (ADR-2026-10-30-1229).

A build has two assembly files. One holds the module's functions and becomes
the object file. The other holds the executable's entry point and runtime.
Both end with `.note.GNU-stack`, so the stack is not executable.

`as --64` assembles each file. `ld -m elf_x86_64 -static` links the two objects
into a static executable with the entry point `__funk_start`. Both tools are
told the target, so neither a configured default nor `LDEMULATION` changes the
build. There is no C compiler (ADR-2026-10-30-1229).

A module whose object file references a symbol it does not define links with
the host's shared glibc instead: `ld --dynamic-linker
/lib64/ld-linux-x86-64.so.2 ... -lc`, still entered at `__funk_start`. That
needs glibc's development files. Any other module stays static, with no C
library (ADR-2026-11-10-1303).

`funk build -o OUTPUT FILE` writes `OUTPUT.o` and `OUTPUT`. The intermediate
files go to a temporary directory, which funk removes. ADR-2026-10-30-1326 says
how the outputs are moved into place.

A tool that prints is a tool that failed. If `as` or `ld` cannot run, exits
with an error or prints anything, the build fails with a `tool-error`.

GNU binutils is not pinned. So a release that adds a warning fails `funk build`
until the backend's output avoids it (ADR-2026-10-30-1229).

## Values and widths

A value of `iN`, with `N` at most 64, lives in one 64-bit register or slot. Its
low `N` bits are its bits, and the bits above are unspecified. This holds in
slots, in scratch registers, and for arguments and results
(ADR-2026-10-30-1231). The one exception is a returned `i1`, which the backend
returns as 0 or 1 in all 64 bits (ADR-2026-10-30-1232, ADR-2026-11-03-0109).
No caller may rely on that for an unmarked `i1` (ADR-2026-11-11-1019).

`add`, `sub`, `mul`, `and`, `or`, `xor`, `trunc`, `select` and `freeze` work on
all 64 bits and extend nothing. Their result's low `N` bits depend only on
their operands' low `N` bits.

Other ops first extend what they read, by sign or by zero as the op reads it.
These are comparisons, `zext`, `sext`, the value of a right shift, and the
amount of every shift. `width::extend` is the one place that knows the
instructions (ADR-2026-10-30-1231).

Division below `i128` extends nothing except at `i1` (ADR-2026-10-31-0050). A
branch or a `select` on an `i1` tests bit 0 (ADR-2026-10-30-1231).

`width::check` accepts `i1`, `i8`, `i16`, `i32`, `i64`, `i128`, `f32` and
`f64`. Every other width or float format is reported as unsupported where its
value is defined (ADR-2026-10-30-1231, ADR-2026-11-03-010730,
ADR-2026-11-11-1140).

A value of `f32` or `f64` lives in one slot or SSE register. Its low 32 or 64
bits are its bits, and the bits above are unspecified, as for an `iN`. A float
constant is written to its slot as an integer immediate of its bits. `fcmp`
loads its operands with `movss` or `movsd` into `%xmm0` and `%xmm1`, compares
them with `ucomiss` or `ucomisd`, and reads the flags with one `setCC`, or two
for `oeq` and `une`, which also test the parity flag that an unordered pair sets
(ADR-2026-11-11-1140). x86-64-backend-lowering.md says how the float arithmetic
lowers, with SSE2 and, for `fma`, a routine of a runtime helper
(ADR-2026-11-11-1802).

An `i128` is two eightbytes. Each half is 64 bits of the value, and no bit is
unspecified (ADR-2026-11-03-010730).

## Frames and slots

Register allocation is spill-everything. Every value has its own slots below
`%rbp`. The parameters come first, then each block's arguments and each op's
results, in order (ADR-2026-10-30-1230).

A value of at most 64 bits takes one 8-byte slot, and the `n`-th slot is at
`-8n(%rbp)`. An `i128` takes two slots next to each other. Its low half is at
the lower address, so its 16 bytes are little-endian (ADR-2026-11-03-010730).

Below the values' slots, a frame holds the address of its own result area when
its results go in memory. It also holds the address it passes to a call that
returns in memory. At its bottom is the area for its calls. That area is as
large as the largest any call needs, and is 16-byte aligned
(ADR-2026-11-03-0109).

The prologue is `pushq %rbp; movq %rsp, %rbp`, then room for the frame. The
epilogue is `leave; ret`. Every frame size is a multiple of 16. A frame must
fit 2 GiB. A function with more values is reported as unsupported
(ADR-2026-10-30-1230).

A frame of less than a page is one `subq`. A frame of 4096 bytes or more is
probed. `frame::prologue` moves `%rsp` down a page at a time and touches each
page with `orq $0, (%rsp)`. It counts pages in `%r11`, then subtracts the rest
(ADR-2026-11-02-1102, ADR-2026-10-30-1230).

So every stack access is at most a page below one already made, a call's first
write included. A frame too large for its stack faults at the stack's end.

An op loads its operands from their slots into scratch registers, computes, and
stores its results into their slots. No value stays in a register from one op
to the next. Scratch registers are caller-saved: `%rax`, `%rcx`, `%rdx` and the
argument registers. So a function saves only `%rbp` (ADR-2026-10-30-1230).

A funk function that C code calls runs on its caller's stack. A frame larger
than what is left there ends with `SIGSEGV` (ADR-2026-10-30-1230,
ADR-2026-11-02-1132).

## The function ABI

### Convention and symbols

A funk function is a System V AMD64 function and a global function symbol.
`%rsp` is 16-byte aligned at each call. `%rbx`, `%rbp` and `%r12` to `%r15` are
callee-saved (ADR-2026-10-30-1232).

A fir name that is a word starting with a letter is its own symbol. A word
holds letters, digits, `_` and `.`. Every other name is `__funk_sym_` followed
by its UTF-8 bytes in lower-case hexadecimal. So `@"a b"` is
`__funk_sym_612062`. The mapping is one-to-one, and never gives a name that the
toolchain or funk's runtime defines (ADR-2026-10-30-1232).

C can call a function whose name is a word starting with a letter, by that
name. Exact link names for a C++ frontend will take a new ADR
(ADR-2026-10-30-1232).

### Arguments

Integer arguments go in `%rdi`, `%rsi`, `%rdx`, `%rcx`, `%r8` and `%r9`, then on
the stack. A funk function reads only the low `N` bits of each `iN` argument
(ADR-2026-10-30-1232). An `f32` or `f64` argument takes the next of `%xmm0` to
`%xmm7`, counted apart from the integer registers, then the next eightbyte of
the stack, in the order of the arguments (ADR-2026-11-11-1140).

`abi::layout` maps a call's arguments, each of one or two eightbytes, to their
places by System V's rules. An `i128` goes in two registers when two are free.
Otherwise all of it goes on the stack, aligned to 16 bytes. A register left
free goes to a later argument. The stack area is padded to a multiple of 16.

The caller, the prologue and the stack figure all read this one layout, so they
cannot disagree. The caller pushes the stack area from the top down, high half
before low half. The callee stores each eightbyte from its register or from
`16 + offset(%rbp)` (ADR-2026-11-03-0108).

### Results

fir functions and calls have any number of results (ADR-2026-10-30-0816). A
funk function returns them as System V returns a C structure with one member
per result, in order. C can call it as such a function
(ADR-2026-11-03-0109).

Each member is aligned to 8 bytes, or to 16 for an `i128`. A result of at most
64 bits takes one eightbyte. An `i128` takes two, its low half first.

A function with no results returns nothing. One or two eightbytes come back in
registers, the first in `%rax` and the second in `%rdx`. So one `i128` comes
back in `%rdx:%rax` (ADR-2026-11-03-0109). An `f32` or `f64` eightbyte is of
class SSE and comes back in the next of `%xmm0` and `%xmm1` instead, so
`f64, i64` comes back in `%xmm0` and `%rax`, as C returns `struct { double a;
long b; }` (ADR-2026-11-11-1140).

Three eightbytes or more all go in memory. The caller passes the address of a
result area as the first argument, in `%rdi`. The call's own arguments follow
it, and an `i128` argument looks for its pair from `%rsi` on
(ADR-2026-11-03-0108).

The callee's `ret` writes every result to the area and returns the address in
`%rax`. The caller copies each result into its slot right after the call. An
`iN` result is in the low `N` bits of its eightbyte. An `i1` is 0 or 1 in all
64 bits, which no caller relies on unless it is marked (ADR-2026-11-11-1019).
The caller stores each eightbyte as it comes, with no extension.
`crates/funk-x86-64/src/abi/results.rs` lays out and emits both sides
(ADR-2026-11-03-0109).

### Calls between funk functions

A call between funk functions passes each argument as its slot holds it, all
64 bits. It extends no argument, at any width. The caller stores `%rax` in the
result's slot as it is (ADR-2026-11-02-1021). M1's optional markers let a
signature ask for an extension. semantics-m1-design.md has that design
(ADR-2026-11-09-1547).

`abi::call` is the one emitter of outgoing funk calls. It owns register
selection, reverse pushes, padding, symbol spelling and cleanup. Fir call
lowering and the entry wrapper both use it. Both restore outgoing space right
after the call. The emitter returns its peak outgoing argument bytes
(ADR-2026-11-02-1428).

The wrapper's calls of the runtime and calls of the `i128` division routines
are plain `call`s, outside `abi::call` (ADR-2026-11-03-0415).

### Code that funk did not compile

In M0, fir has no item that declares a function defined elsewhere. So every fir
`call` reaches a function of the module (ADR-2026-11-02-1021). M1's external
declarations change that. Their design is in semantics-m1-design.md
(ADR-2026-11-09-1547).

C callees expect more of a narrow argument than a funk callee does. They read an
`i8` or `i16` argument as extended to 32 bits, as the C type requires. They read
an `i1` as 0 or 1 in at least its low 8 bits (ADR-2026-10-30-1232).

fir types carry no sign, so an extension needs a marker (ADR-2026-11-02-1021).
ADR-2026-11-09-1547 defines it. An integer parameter or result narrower than 32
bits may carry `sext` or `zext`. The marker is optional, and frontends set it to
match the C ABI. The backend extends a marked argument at the call and a marked
result at the return, and nothing unmarked. An `i1` marked `zext` is a C
`_Bool`. With no marker, neither side may rely on the upper bits.

Code that calls a C function may rely only on bit 0 of an unmarked `i1` result
(ADR-2026-10-30-1232). A caller that needs a C `_Bool`, 0 or 1 in `%al`, relies
on the `zext` marker. The backend still returns an unmarked `i1` as 0 or 1 in
all of `%rax`, but no caller, funk's own code included, relies on the bits above
bit 0 (ADR-2026-11-11-1019).

## Poison

Any value refines poison (ADR-2026-10-29-2008). The op `poison` gives a poison
result (ADR-2026-11-03-1615).

Native code has no poison value: every value is the bits in its slot. An op
whose source result is poison still stores some bits, and nothing relies on
which. `add`, `sub` and `mul` lower the same with any flags as without, and no
code tests a flag (ADR-2026-10-30-2248).

`freeze` is a copy. It loads its operand's slot and stores the bits in its own.
Only the `freeze` writes that slot, so every use sees the same bits. A `freeze`
that runs twice may give other bits each time (ADR-2026-10-30-2248).

The op `poison` writes zero into each eightbyte of its result's slot, with
`movq $0`. A fixed value keeps native runs reproducible. `freeze` uses no fixed
value, since code cannot know at run time whether a value is poison
(ADR-2026-11-03-1616).

## Lowering `i128` and division

How the backend lowers `i128` and the divisions is on
x86-64-backend-lowering.md.

## `select`, branches and block arguments

Below `i128`, `select` is one `cmov`, with no branch. It tests bit 0 with `testb $1, %cl`.
When the bit is clear, `cmovzq` moves in the second value from its slot. Nothing
of the condition above bit 0 is read (ADR-2026-10-31-0215).

A function's blocks are laid out in the order of its body, each at a label such
as `.Lb0_loop`. `br` copies its block arguments, then jumps unless its block
comes next. `cond_br` tests bit 0 with `testb $1, %al` before any copy. A `jnz`
or `jz` then goes to one edge, and the code of the other edge follows it. A
branch on poison goes one way or the other (ADR-2026-10-31-0334).
`unreachable` is `ud2`. A run that reaches it is UB, so any code would do, and
`ud2` stops the run instead of falling into the next block. This is a choice of
the naive backend, recorded in the doc comment of `lower/control.rs`.

A branch copies the values it passes as one parallel move. `moves.rs` turns an
edge's copies into steps. It drops a copy from a slot to itself. It then does
each copy whose destination no remaining copy reads. The copies left form
cycles. The first remaining destination is saved in `%rcx`, which opens its
cycle into a chain. Every copy moves all 64 bits (ADR-2026-10-31-0335).

## The built executable

`OUTPUT @FUNCTION ARG...` runs one function, with one argument per parameter. An
argument is `true` or `false` at `i1`, and otherwise signed decimal. An `f32` or
`f64` is its bits read as a signed integer, read and printed as an `i32` or
`i64` is: a spelling internal to the harness, which converts it to and from
the float literals of fir text (ADR-2026-11-11-1438). On success
it prints one line such as `{"values":["V1","V2"]}` and exits with 0
(ADR-2026-10-30-1233).

Exit status 2 never means a result. Bad usage, an unreserved stack and a failed
write to standard output all exit with 2. All but the failed write print one
line to standard error. A function that crashes ends by a signal, with nothing
on standard output (ADR-2026-10-30-1233).

The entry file holds a runtime in assembly with no libc, in `entry/runtime.s`
and `entry/values.s` (ADR-2026-11-03-0108). For each function it adds a wrapper
and a table entry by fir name. The wrapper parses the arguments and calls the
function. It passes each result, sign-extended, to the printer
(ADR-2026-10-30-1233).

The runtime uses only `write`, `mmap`, `mprotect`, `rt_sigaction`, `exit_group`,
`getrlimit`, `sysinfo`, `sigaltstack`, `rt_sigprocmask`, `rt_sigreturn`,
`getpid` and `kill` (ADR-2026-10-30-1233, ADR-2026-11-02-1132).

When the program links with glibc, the runtime also registers the loader's
finalizer with `__cxa_atexit`. It calls `fflush(NULL)` before it writes
standard output, so C's output comes before the values line, and a failed
flush exits with 2. A successful run leaves through `exit(0)`. Every other exit
stays `exit_group`, which keeps what C already wrote out but loses what it
still buffers (ADR-2026-11-10-1303).

### The run's stack

The function runs on a stack that the runtime reserves with `mmap`, using
`MAP_NORESERVE`, above a guard page (ADR-2026-10-30-1233).

The table gives each function a figure, rounded up to a page. It holds the
wrapper's return address, saved `%rbp`, frame and stack arguments, 16 KiB for
the runtime, and the function's need. A function's need is 16 bytes and its frame. To that it adds the largest,
over its calls, of what the call pushes plus the callee's need
(ADR-2026-11-02-1132).

`entry/stack.rs` counts pushed words from the layout that `abi::call` reads
(ADR-2026-11-03-0108). A division at `i128` or an `fma` at `f32` or `f64`
counts as a call needing 24 bytes, the most that a runtime helper's routine
uses (ADR-2026-11-03-0415, ADR-2026-11-11-1802).

Calls within a cycle do not count. A function from which no cycle is reachable
gets exactly its figure, whatever `ulimit -s` says. A function from which a
cycle is reachable is recursive. It reserves the smaller of the soft
`RLIMIT_STACK` and memory plus swap, and never less than its figure. `ulimit -s
unlimited` leaves memory and swap as the bound.

When `mmap` refuses, the runtime halves its request, down to the figure. When
even the figure is refused, it reports that it cannot reserve the stack.

A run that outgrows its stack says so. The runtime catches `SIGSEGV` on a stack
of its own. A fault in the guard page prints
`PROGRAM: @f ran out of the N bytes of stack reserved for it` and exits with 2.
Standard output stays empty. Any other `SIGSEGV` ends the process as a crash
does (ADR-2026-11-02-1132).

## What later work must keep

A register allocator must treat as clobbered:

- `%rax`, `%rcx` and `%rdx` by a division (ADR-2026-10-31-0050).
- `%rax`, `%rcx`, `%xmm0` and `%xmm1` by an `fcmp` (ADR-2026-11-11-1140).
- `%xmm0` by a float op of arithmetic, `%rax` by `fneg` and `fabs`, and every
  caller-saved register by an `fma` (ADR-2026-11-11-1802).
- `%rax` and `%rcx` by a branch (ADR-2026-10-31-0334).
- `%rax`, `%rcx` and `%rdx` by an `i128` op, and `%rsi` by a shift
  (ADR-2026-11-03-010730).
- Every caller-saved register by an `i128` division (ADR-2026-11-03-0415).

Block arguments in registers need the same sequencing, and a scratch register
or an exchange for each cycle (ADR-2026-10-31-0335).

An optimizer that makes poison real must keep each `freeze` one value that every
use reads (ADR-2026-10-30-2248). The two halves of a frozen `i128` stay one
value (ADR-2026-11-03-010730).

It must read only bit 0 of every `i1`. No optimizer may turn a `select` into a
`cond_br` without freezing its condition first (ADR-2026-10-31-0215).

It must not make a division run where the source would not
(ADR-2026-10-31-0050). It may lower `poison` to anything, or fold it away
(ADR-2026-11-03-1616).
