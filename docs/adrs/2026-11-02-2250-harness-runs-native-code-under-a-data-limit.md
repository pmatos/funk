# The harness runs the executable of a differential test, and only it, under a data limit of 1 GiB

Status: accepted

## Context

ADR-2026-10-30-2049's harness runs every process through `tools.run`,
with a 120-second timeout and no memory limit: `funk verify`,
`funk build` (which runs `as` and `ld`), `fir-ref` and the executable
of each differential test. A built executable runs its function on a
stack that it maps with `mmap` (ADR-2026-10-30-1233).

[PR #90](https://github.com/pmatos/funk/pull/90) lets a recursive run
reserve more: up to the process's stack limit, `ulimit -s`, and memory
and swap under `ulimit -s unlimited`. A native run that recurses without
end, from a backend miscompile or a test that counts down from -1, then
uses its stack until it runs out. With no limit, a large reservation
fills memory and then swap until an OOM killer ends it, and a userspace
one such as `systemd-oomd` ends the whole cgroup, which can hold the
harness and the shell that started it
([#92](https://github.com/pmatos/funk/issues/92)).

## Decision

- **Only native code.** `tools.run_native` runs a built executable as
  `tools.run` does, with `tools.limit_data` as its `preexec_fn`, and
  `Harness.test` runs each differential test's executable with it.
  `funk`, `fir-ref`, `as` and `ld` run as before: they build and judge,
  and are not the code under test.
- **Both limits, soft and hard.** In the child, `limit_data` sets
  `RLIMIT_DATA` (`ulimit -d`), which bounds private writable mappings
  such as the stack the runtime maps, and `RLIMIT_AS` (`ulimit -v`),
  which bounds every mapping, `MAP_NORESERVE` ones included. A hard limit
  equal to the soft one keeps the executable from raising it.
- **1 GiB, `tools.DATA_LIMIT`.** It is far more than a run of the corpus
  needs: its code, and a stack of its frames and 16 KiB, or at most
  `ulimit -s`, 8 MiB by default, under PR #90. Under
  `ulimit -s unlimited`, PR #90's runtime asks for memory and swap,
  `RLIMIT_AS` refuses, and the runtime halves its request until one
  fits. So a valid test still runs, on a stack below 1 GiB, and a
  runaway one still ends at its guard page with exit status 2. The
  harness relies on that halving there: a runtime that gave up at the
  first refusal would exit with 2 on every recursive test. 1 GiB is far
  less than a CI runner's memory, so a runaway run ends long before
  memory or swap fill. One fixed size, so a verdict does not depend on
  the machine. When the harness already runs under a lower soft limit,
  the child keeps that one: the limit never loosens, and setting it
  never fails.
- **The verdicts do not change.** A run that cannot reserve its stack
  exits with 2 (ADR-2026-10-30-1233), and one that outgrows it exits
  with 2 under PR #90 or dies by `SIGSEGV`. `tools.native_values` reads
  either as a failure: the test is invalid where `fir-ref` runs out of
  fuel, and fails where it returns (ADR-2026-10-30-2135,
  ADR-2026-10-31-0003). The timeout, the verdict rules and the corpus
  stay as they are.

## Alternatives

- **The limit in `tools.run`, on every tool.** A check would then fail
  for what a tool needs, not for what the code under test does; #92
  keeps the limit off `fir-ref`, `funk build`, `as` and `ld`.
- **A cgroup memory limit** (`systemd-run --scope -p MemoryMax=`). It
  needs a systemd manager, which not every host that runs the hook has;
  Python's `resource` needs nothing more.
- **A size from the machine's memory.** A test could then pass on one
  host and fail on another.

## Consequences

- A runaway native run ends after at most 1 GiB, and the harness and
  its shell survive it.
- A test whose executable needs more than 1 GiB fails, or is invalid,
  as above. Raising `DATA_LIMIT` takes a new ADR.
- `preexec_fn` runs in the child between `fork` and `exec`, which Python
  documents as unsafe in a process with threads; the harness has none.
- `test_tools.py` checks that a child of `run_native` runs under the
  limit, maps below it and cannot map past it, and keeps a lower limit
  that it inherits, and that a child of `run` keeps the harness's
  limits. In `test_main.py`, the executable that the stand-in for
  `funk` builds prints its values only under a limit, and each stand-in
  for `funk` and `fir-ref` fails unless it runs under the harness's own
  limits. So a harness that ran native code with `run`, or a tool with
  `run_native`, would fail the test.
