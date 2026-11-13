# Current decisions: the x86-64 backend, the built executable

This page continues [x86-64-backend.md](x86-64-backend.md). It says what holds
today for the executable that `funk build` writes: how it runs one function,
its runtime, and the stack it runs the function on. It is the record: when this
page and an ADR disagree, the page wins, and the ADR is fixed or deleted
(ADR-2026-11-09-1610).

## Running one function

The differential harness calls a built function with arguments and reads its
values, to compare them with `fir-ref`'s. `OUTPUT @FUNCTION ARG...` runs one
function. It names the function as fir's text writes it, quoted when it is not
a word (`@add3`, `@"a b"`), and gives one argument per parameter.

An argument is the spelling of a constant of its parameter's type: `true` or
`false` at `i1`, and otherwise signed decimal with no leading zeros, no `+` and
no `-0`, in the type's range. An `f32` or `f64` is its bits read as a signed
integer, read and printed as an `i32` or `i64` is: a spelling internal to the
harness, which converts it to and from the float literals of fir text
(ADR-2026-11-11-1438).

On success it writes one line to standard output, `{"values":["V1","V2"]}`, a
JSON list of the returned values in order, each a string with the same
spelling, and exits with 0. A function with no result prints `{"values":[]}`.
Strings keep wide values exact for any JSON reader.

Exit status 2 never means a result. An unknown function, a wrong number of
arguments, an argument that is not a value of its type, or a stack that cannot
be reserved prints one line to standard error, such as `PROGRAM: 128 is not a
value of type i8`, nothing to standard output, and exits with 2. Text from the
command line, such as the program's path, the function's name or an argument,
shows each control byte, below 0x20 or 0x7f, as `\xHH`, so the message stays on
one line. A failed write to standard output also exits with 2, with no message.
The executable ignores `SIGPIPE`, so a reader that closed the pipe gives that
status, not a signal.

A function that crashes, as a division by zero does, ends by a signal, with
nothing on standard output.

Rejected: calling the function from the test process, since loading generated
code needs `unsafe`, which the workspace forbids; a generated C `main`, which
needs a C compiler and libc; and bare numbers in the JSON list, since `i1`
would read as JSON booleans and `i64` values past 2^53 lose precision in many
JSON readers.

## The entry file and its runtime

The entry file holds a runtime in assembly that needs no libc,
`crates/funk-x86-64/src/entry/runtime.s` and `entry/values.s`, which follows it
in the entry file. The value routines moved to `values.s` to keep `runtime.s`
within the file-size budget. For each function the entry file adds a wrapper,
and a table of the functions by their fir names. The wrapper parses the
arguments, calls the function through `abi::call` and passes each result,
sign-extended from its width, to the printer. It parses an `i128` argument into
two slots, and passes `%rdx`, an `i128` result's high half, to the printer.
The runtime's routines that parse arguments and print results work on 128 bits
at every width.

The runtime uses only the Linux system calls `write`, `mmap`, `mprotect`,
`rt_sigaction`, `exit_group`, `getrlimit` (97), `sysinfo` (99), `sigaltstack`
(131), `rt_sigprocmask` (14), `rt_sigreturn` (15, in the restorer that x86-64
requires of a handler), `getpid` (39) and `kill` (62).

When the program links with glibc
([x86-64-backend.md](x86-64-backend.md#linking-with-the-host-c-library)), the
entry file starts with `.set .Lfunk_libc, 1`, which turns on parts of
`entry/runtime.s`. The entry point stays the runtime's `__funk_start`. The
dynamic loader runs glibc's own initialisers before it, so stdio, `environ` and
thread-local storage work. `__funk_start` registers the loader's finalizer,
which it finds in `%rdx`, with `__cxa_atexit`, as glibc's `__libc_start_main`
does. glibc's start-up code and `main` are not used.

Before the runtime writes standard output, it calls `fflush(NULL)`, so what the
function wrote through C's stdio comes before the values line. When the flush
fails, the program exits with 2, as on any failed write. A successful run
leaves through `exit(0)`, which runs the C library's exit handlers. Every other
way out stays `exit_group`, the stack overflow's handler among them, so the exit
statuses and messages on this page hold.

So a run that ends with status 2 loses what C's stdio still buffers, but not
what it already wrote: C writes a full buffer, or a line to a terminal, on its
own. After a stack overflow, standard output is empty only when the function
wrote nothing that C wrote out. Output from C's exit handlers comes after the
values line, and a failure to write it leaves the status at 0.

## The run's stack

The function runs on a stack that the runtime reserves for it, not on the
process's stack, so `ulimit -s` does not bound a frame: the backend's 2 GiB
does. The runtime maps the stack with `mmap`, using `MAP_NORESERVE`, so pages
that are never touched cost nothing. It makes the page below it a guard page,
and calls the wrapper with `%rsp` at its top. A run touches only the pages its
frames use, so a large stack costs address space, not memory.

Rejected: running on the process's stack and checking `getrlimit` first, since
the check cannot know how much of the limit the arguments and environment use,
and a frame larger than the limit could never run.

### The figure

The table gives each function a figure, rounded up to a page and at most 2^62.
It holds the wrapper's return address, saved `%rbp`, frame and stack
arguments, 16 KiB for the runtime, and the function's need. A function's need
is 16 bytes for its own return address and saved `%rbp`, and its frame. To that
it adds the largest, over its calls, of what the call pushes plus the callee's
need. The callee is the first function of its symbol.
`crates/funk-x86-64/src/lower/stack.rs` computes it from emitted call facts.

The figure follows the lowering. `lower/call.rs` records each callee and the
peak outgoing argument bytes returned by `abi::call`, including padding and
the result area's address. Lowering also records runtime-helper use while it
emits ops and includes each required helper's assembly once. Any helper counts
as a call that pushes no argument and needs `HELPER_STACK`, 24 bytes, the most
that a routine of a runtime helper uses
([x86-64-backend-lowering.md](x86-64-backend-lowering.md#division-at-i128)).
Lowering returns complete stack needs in function order; entry generation
owns the wrapper, runtime allowance and rounding, without reconstructing call
placement or helper use from fir. The graph calculation stays iterative and
uses saturating arithmetic.

The figure counts nothing for a C function's own frames, only the runtime's
16 KiB; #239, which adds calls to C, decides what a C callee's stack counts.

Calls within a cycle do not count: a call between two functions of one
strongly connected component of the call graph is left out. What is left has
no cycle, so each need is a sum along the deepest path. A function from which
no cycle is reachable gets exactly its figure, whatever `ulimit -s` says, and
never outgrows its stack.

### A recursive run

A function from which a cycle is reachable is recursive. Its figure is then the
most a run uses when it makes no call within a cycle, and the least the runtime
reserves for it. The runtime reads the soft `RLIMIT_STACK` with `getrlimit`,
rounded down to a page, and reserves the smaller of it and the machine's memory
and swap, from `sysinfo`, never less than the figure. `RLIM_INFINITY` (`ulimit
-s unlimited`) leaves memory and swap as the bound, as does a failed
`getrlimit`. So by default a recursive run gets 8 MiB, as a C or Rust program
does, or its figure when that is more.

When `mmap` refuses, as under `ulimit -d` or `ulimit -v`, the runtime halves
its request, down to the figure. When even the figure is refused, it reports
`PROGRAM: cannot reserve N bytes of stack for @f`, with N the figure.

The human ruled on 2026-11-02, on PR #90, with option 2 of three: a recursive
run caps the stack it reserves at the process's stack limit, `ulimit -s`, and
reports that it ran out of stack when it outgrows it. `ulimit -s unlimited`
lifts the cap to memory and swap, so fir keeps no depth limit of its own.

Rejected: as much stack as memory and swap with no cap, the first version,
which let a recursion without end fill memory and swap before it reported, and
could take the session that started it down with it. Also rejected: a fixed cap
of fir's own, a depth limit or a knob users do not know; capping every run at
`ulimit -s`, since a function that cannot outgrow its figure gains nothing and
a large frame could never run; capping a recursive run below its figure; growing
the stack on demand from a `PROT_NONE` reservation, which goes no deeper under
default overcommit; and a check of `%rsp` in each prologue, which costs two
instructions in every call where the guard page costs nothing.

Under `ulimit -s unlimited`, a run that recurses without end fills memory and
swap under default overcommit, until an OOM killer ends it. The report comes
first only when `ulimit -d` or `ulimit -v`, or strict overcommit, makes the
stack smaller than what is free. A cgroup's memory limit (`memory.max`) is not
such a limit: `sysinfo` reports the host's memory. Under strict overcommit
(`vm.overcommit_memory = 2`) `MAP_NORESERVE` is ignored, so a recursive run
commits its whole stack for as long as it runs. The harness runs native code
under a data limit
([testing-and-harness.md](testing-and-harness.md#native-code-runs-under-a-data-limit)),
so there the halving makes the stack fit and the run still ends.

### A run that outgrows its stack

A run that outgrows its stack says so. Every stack access is at most a page
below one already made
([x86-64-backend.md](x86-64-backend.md#stack-probes)), so such a run faults
first in the guard page.

Before it calls the wrapper, the runtime catches `SIGSEGV` on a 64 KiB stack of
its own (`sigaltstack`), with `SA_SIGINFO`, `SA_ONSTACK`, `SA_RESETHAND` and
`SA_RESTORER`, and unblocks it, since a parent can leave it blocked across
`execve`. A fault whose address is in the guard page prints `PROGRAM: @f ran out
of the N bytes of stack reserved for it`, with N the bytes reserved and the
names shown as above, and exits with 2. It never writes the buffered output, so
standard output stays empty.

Any other `SIGSEGV` is not an overflow, and the default action is back. The
handler returns, so the instruction faults again and ends the process with the
fault's own code and address, as a crash does. A `SIGSEGV` that a process sent,
the handler sends again with `kill` before it returns. Rejected: keeping the
bare crash, which does not say why the run ended.
