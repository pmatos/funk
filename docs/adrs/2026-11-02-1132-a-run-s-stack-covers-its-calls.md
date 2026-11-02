# A run's stack covers its calls, a recursive run gets as much as memory allows, and a run that outgrows its stack says so

Status: accepted

## Context

ADR-2026-10-30-1233 runs each function of a built executable on a stack
that the runtime reserves with `mmap` (`MAP_NORESERVE`, so untouched pages
cost nothing), with a guard page below it. The table of functions sizes
that stack from the function's own frame, its wrapper's and 16 KiB. It
leaves to [#20](https://github.com/pmatos/funk/issues/20) how the figure
covers callees, and with recursion their arguments, and what a run that
outgrows its stack reports.

- A call pushes the arguments past the sixth, padded to an even number,
  and then its return address, below the caller's frame
  (ADR-2026-10-30-1232). Each frame is at most 2 GiB
  (ADR-2026-10-30-1230); a chain of calls has no such bound.
- Every access to the stack is at most a page below one made before it
  (ADR-2026-10-30-1230, ADR-2026-11-02-1102), so a run that outgrows its
  stack faults first in the guard page.
- How deep a recursion goes depends on its arguments, so no figure from
  the code bounds it.
- fir has no depth limit, as it has no nesting limit
  (ADR-2026-10-30-1549): a valid program should not fail for want of stack
  while memory allows. No specific depth or stack size is an acceptance
  bar.

These points are one decision, the one ADR-2026-10-30-1233 leaves to
[#20](https://github.com/pmatos/funk/issues/20): the figure says which runs
can outgrow their stack, the reservation how far a recursive run goes, and
the report what a run that still outgrows it says.

## Decision

- **The figure covers every call.** The table gives each function the
  bytes a run of it needs, rounded up to a page and at most 2^62: the
  wrapper's return address, saved `%rbp`, frame and stack arguments,
  16 KiB for the runtime, and the function's need. A function's need is
  16 bytes for its own return address and saved `%rbp`, its frame, and
  the largest, over its calls, of the bytes the call pushes plus the
  callee's need. The callee is the first function of its symbol.
  `crates/funk-x86-64/src/entry/stack.rs` computes it.
- **Calls within a cycle do not count.** A call between two functions of
  one cycle of calls (a function that calls itself, or functions that
  call each other: one strongly connected component) is left out. What is
  left has no cycle, so each need is a sum along the deepest path. For a
  function from which no cycle is reachable, that is the most any run
  uses, and the runtime reserves exactly the figure, as before.
- **A recursive run gets as much stack as memory allows.** The table marks
  a function from which a cycle is reachable as recursive; its figure is
  then the most a run uses when it makes no call within a cycle, and the
  least the runtime reserves for it. The runtime asks `mmap` for the
  machine's memory and swap, from `sysinfo`, rounded down to a page and
  never less than the figure. When
  `mmap` refuses, as under `ulimit -d` or `ulimit -v`, it asks for half
  as much, down to the figure. When even the figure is refused, it reports
  `PROGRAM: cannot reserve N bytes of stack for @f`, with N the figure,
  as ADR-2026-10-30-1233 does.
- **An overflow is reported.** Before it calls the wrapper, the runtime
  catches `SIGSEGV` on a 64 KiB stack of its own (`sigaltstack`), with
  `SA_SIGINFO`, `SA_ONSTACK`, `SA_RESETHAND` and `SA_RESTORER`, and
  unblocks it, since a parent can leave it blocked across `execve`. A fault
  whose address is in the guard page is a run that outgrew its stack. The
  handler writes one line to standard error,
  `PROGRAM: @f ran out of the N bytes of stack reserved for it`, with N
  the bytes reserved, the program's path and the function's name shown as
  ADR-2026-10-30-1233 shows them (each control byte as `\xHH`), and exits
  with 2. It never writes the buffered output, so standard output stays
  empty. Any other `SIGSEGV` is not an overflow, and the default action is
  back. After any other fault the handler returns, so the instruction
  faults again and ends the process with the fault's own code and address,
  as a crash did before. A `SIGSEGV` that a process sent, the handler sends
  again with `kill` before it returns.
- **New system calls.** The runtime now also uses `sysinfo` (99),
  `sigaltstack` (131), `rt_sigprocmask` (14), `rt_sigreturn` (15, in the
  restorer that x86-64 requires of a handler), `getpid` (39) and `kill`
  (62). It still uses no libc.

## Alternatives

- **A fixed stack for recursion**, such as 8 MiB or 1 GiB. A runaway
  recursion would end fast with the report, but a valid program would fail
  for want of stack while memory allows: a depth limit by another name.
- **`ulimit -s` for recursion.** The usual knob, but 8 MiB by default:
  the same limit.
- **A fixed huge reservation**, such as half the address space. The same
  reach, but a number with no meaning, and no machine can fill it.
- **Grow the stack on demand** from a `PROT_NONE` reservation, in the
  handler. Under default overcommit it goes no deeper than
  `MAP_NORESERVE`; it helps only strict overcommit, for much more code.
- **Bound a recursion by its arguments.** Undecidable in general.
- **Compare `%rsp` with a limit in each prologue.** Two instructions in
  every call; the guard page catches an overflow for nothing.
- **Keep the crash.** A bare `SIGSEGV` does not say why the run ended.

## Consequences

- A run of a function from which no cycle is reachable never outgrows its
  stack, whatever its calls.
- A recursive run goes as deep as memory allows. Under default
  overcommit its stack is as large as memory and swap, so a run that
  recurses without end fills memory and then swap, slowing the whole
  machine, until an OOM killer ends it, usually before it reaches the
  guard page. The kernel's OOM killer usually picks the run. A userspace
  one, such as `systemd-oomd`, ends the whole cgroup the run is in, so the
  shell, terminal or harness that started it ends too.
- The report comes instead when a limit makes the stack smaller than what
  is free: `ulimit -d` or `ulimit -v`, or strict overcommit. A cgroup's
  memory limit (`memory.max`) is not such a limit: `sysinfo` reports the
  host's memory, and the cgroup's OOM killer ends the run. So anything that
  may recurse without end runs under `ulimit -d` or `ulimit -v`; the tests
  that do run under both.
- Under strict overcommit (`vm.overcommit_memory = 2`) `MAP_NORESERVE` is
  ignored, so a recursive run commits more than half of what the system has
  left, for as long as it runs, however shallow it is. Meanwhile other
  processes' allocations can fail.
- A run touches only the pages its frames use: a large stack costs
  address space, not memory.
- The figure follows the lowering: `lower/call.rs` gives both a call's
  callee and the words it pushes.
- The differential harness runs a test's native executable with only a
  timeout. A native run that outgrows its stack exits with 2, a failure
  where `fir-ref` returns. But a differential test whose recursion never
  ends natively, such as a count-down called with -1 or a miscompiled
  recursive function, would fill memory as above, and an OOM killer could
  end the harness with it. So the harness must run native code under a
  data limit before the corpus adds a differential test through a
  recursive call ([#92](https://github.com/pmatos/funk/issues/92)); until
  then such tests stay interpreter-only.
- A funk function that C code calls still runs on its caller's stack
  (ADR-2026-10-30-1230).
