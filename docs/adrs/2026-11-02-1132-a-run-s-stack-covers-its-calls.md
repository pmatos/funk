# A run's stack covers its calls, a recursive run's stack follows `ulimit -s`, and a run that outgrows its stack says so

Status: accepted; refined by ADR-2026-11-03-0108, ADR-2026-11-03-0415 and ADR-2026-11-09-1602
Tier: implementation; area: x86-64-backend

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
- fir has no depth limit of its own, as it has no nesting limit
  (ADR-2026-10-30-1549). No specific depth or stack size is an acceptance
  bar.
- A first version reserved as much stack as memory and swap for a
  recursive run. Under default overcommit, a run that recursed without end
  then filled memory and swap, slowing the whole machine, until an OOM
  killer ended it, usually before the guard page. A userspace OOM killer,
  such as `systemd-oomd`, ends the whole cgroup, with the shell, terminal
  or harness that started the run.
- C and Rust programs run on the process's stack, whose size is the soft
  `RLIMIT_STACK` (`ulimit -s`): 8 MiB by default. Users know that knob.

The question put to the human, on
[PR #90](https://github.com/pmatos/funk/pull/90), was how much stack a
recursive run should reserve, then as much as memory and swap. A run from
which no cycle is reachable reserves exactly its figure, which
ADR-2026-10-30-1233 keeps out of `ulimit -s`, so it was not in question.
The human ruled on 2026-11-02, with option 2 of three: a run caps the
stack it reserves at the process's stack limit, `ulimit -s`, and reports
that it ran out of stack when it outgrows it. `ulimit -s unlimited` lifts
the cap to memory and swap, so fir keeps no depth limit of its own.

These points are one decision, the one ADR-2026-10-30-1233 leaves to
[#20](https://github.com/pmatos/funk/issues/20): the figure says which runs
can outgrow their stack, the reservation how far a recursive run goes, and
the report what a run that outgrows it says.

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
  uses, and the runtime reserves exactly the figure, as before, whatever
  `ulimit -s` says.
- **A recursive run's stack follows `ulimit -s`.** The table marks a
  function from which a cycle is reachable as recursive; its figure is
  then the most a run uses when it makes no call within a cycle, and the
  least the runtime reserves for it. The runtime reads the soft
  `RLIMIT_STACK` with `getrlimit`, rounded down to a page, and reserves
  the smaller of it and the machine's memory and swap, from `sysinfo`,
  never less than the figure. `RLIM_INFINITY` (`ulimit -s unlimited`)
  leaves memory and swap as the bound, as does a failed `getrlimit`.
  When `mmap` refuses, as under `ulimit -d` or `ulimit -v`, the runtime
  asks for half as much, down to the figure. When even the figure is
  refused, it reports `PROGRAM: cannot reserve N bytes of stack for @f`,
  with N the figure, as ADR-2026-10-30-1233 does.
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
- **New system calls.** The runtime now also uses `getrlimit` (97),
  `sysinfo` (99), `sigaltstack` (131), `rt_sigprocmask` (14),
  `rt_sigreturn` (15, in the restorer that x86-64 requires of a handler),
  `getpid` (39) and `kill` (62). It still uses no libc.

## Alternatives

- **As much stack as memory and swap, with no cap.** The first version.
  Any depth by default, but a recursion without end fills memory and swap
  before it reports, and can take the session that started it down with
  it.
- **A fixed cap of fir's own**, such as 8 MiB or 1 GiB. A depth limit, or
  one more knob that users do not know.
- **Cap every run at `ulimit -s`**, recursive or not. A function with a
  frame larger than the limit could never run, which ADR-2026-10-30-1233
  rejects; a function from which no cycle is reachable cannot outgrow its
  figure, so a cap protects nothing there.
- **Cap a recursive run below its figure** when `ulimit -s` is smaller.
  Its frames could not run even when it makes no call within a cycle,
  which ADR-2026-10-30-1233 rejects for any function.
- **A fixed huge reservation**, such as half the address space. A number
  with no meaning, and the same cost as memory and swap.
- **Grow the stack on demand** from a `PROT_NONE` reservation, in the
  handler. Under default overcommit it goes no deeper than
  `MAP_NORESERVE`; it helps only strict overcommit, for much more code.
- **Bound a recursion by its arguments.** Undecidable in general.
- **Compare `%rsp` with a limit in each prologue.** Two instructions in
  every call; the guard page catches an overflow for nothing.
- **Keep the crash.** A bare `SIGSEGV` does not say why the run ended.

## Consequences

- A run of a function from which no cycle is reachable never outgrows its
  stack, whatever its calls, and `ulimit -s` does not bound it.
- By default a recursive run gets 8 MiB, as a C or Rust program does, or
  its figure when that is more. A run that recurses without end reports
  that it ran out within milliseconds, and touches no more than that. A
  valid recursion that needs more stack reports it too, and runs under a
  larger `ulimit -s`.
- Under `ulimit -s unlimited` a recursive run goes as deep as memory and
  swap allow. Then, under default overcommit, a run that recurses without
  end fills memory and swap, slowing the whole machine, until an OOM
  killer ends it, as the first version did by default. The report comes
  first only when `ulimit -d` or `ulimit -v`, or strict overcommit, makes
  the stack smaller than what is free. A cgroup's memory limit
  (`memory.max`) is not such a limit: `sysinfo` reports the host's memory.
- Under strict overcommit (`vm.overcommit_memory = 2`) `MAP_NORESERVE` is
  ignored, so a recursive run commits its whole stack, 8 MiB by default,
  for as long as it runs.
- A run touches only the pages its frames use: a large stack costs
  address space, not memory.
- The figure follows the lowering: `lower/call.rs` gives a call's callee,
  and `abi::pushed_words`, which the call emitter `abi::call` uses
  (ADR-2026-11-02-1428), the words it pushes.
- The differential harness runs a test's native executable under a limit
  of 1 GiB on its data and its address space
  ([#92](https://github.com/pmatos/funk/issues/92),
  [PR #102](https://github.com/pmatos/funk/pull/102)). A native run that
  outgrows its stack exits with 2, a failure where `fir-ref` returns.
  Under the default `ulimit -s` a differential test whose recursion never
  ends natively, such as a miscompiled recursive function, ends at once;
  under `ulimit -s unlimited` the runtime halves its request until the
  stack fits under that limit, so the run still ends, after touching less
  than 1 GiB.
- A funk function that C code calls still runs on its caller's stack
  (ADR-2026-10-30-1230).
