# funk build links with the host's shared C library when the module needs it

Status: accepted
Tier: implementation; area: x86-64-backend

## Context

ADR-2026-10-30-1229 links every program with `ld -m elf_x86_64 -static`
and no C library. M1 needs one: #234 lowers copies to `memcpy`, `memmove`
and `memset`, and #239 calls C functions such as `printf`
(ADR-2026-11-09-1547). A C compiler, musl or any other new tool needs the
human first. On x86-64 Linux, `ld` with GNU binutils can link against the
host's glibc directly. `ld -static` with `libc.a` fails on `_init` and
`_fini` and skips glibc's start-up. The runtime writes standard output with
its own buffer and leaves with `exit_group`, so output that C's stdio still
buffers is lost when standard output is a pipe.

## Decision

- **When.** `funk build` reads the symbol table of the module's object
  file. When the object references a symbol that it does not define, the
  program links with the C library. Otherwise the link is ADR-2026-10-30-1229's,
  unchanged: static, with nothing else, and the same entry file. So the
  module's object must define every routine of funk's own that it calls,
  as it does the `i128` division routines (ADR-2026-11-03-0414): a call
  from the module to a routine of the entry file would link with the C
  library for nothing.
- **Which library, and how.** The host's shared glibc, through `ld`
  alone: `ld -m elf_x86_64 --dynamic-linker /lib64/ld-linux-x86-64.so.2
  -e __funk_start MODULE.o ENTRY.o -lc`. No C compiler, no `crt1.o`.
- **Start-up.** The entry point stays the runtime's `__funk_start`. The
  dynamic loader runs glibc's own initialisers before it, so stdio,
  `environ` and thread-local storage work. `__funk_start` registers the
  loader's finalizer, which it finds in `%rdx`, with `__cxa_atexit`, as
  glibc's `__libc_start_main` does. glibc's start-up code and `main` are
  not used.
- **Output and exit.** The entry file starts with `.set .Lfunk_libc, 1`,
  which turns on parts of `entry/runtime.s`. Before the runtime writes
  standard output, it calls `fflush(NULL)`. So what the function wrote
  through C's stdio comes before the line `{"values":[...]}`. When the
  flush fails, the program exits with 2, as on any failed write. A
  successful run leaves through `exit(0)`, which runs the C library's
  exit handlers. Every other way out stays `exit_group`, the stack
  overflow's signal handler among them, so ADR-2026-10-30-1233's and
  ADR-2026-11-02-1132's exit statuses and messages hold.
- **What standard output holds.** A run that ends with status 2 loses what
  C's stdio still buffers, but not what it already wrote: C writes a full
  buffer, or a line to a terminal, on its own. So after a stack overflow
  standard output is empty only when the function wrote nothing that C
  wrote out. Output from C's exit handlers comes after the values line,
  and a failure to write it leaves the status at 0.

## Alternatives

- **Static glibc, `libc.a`.** Fails to link without glibc's start files,
  and glibc does not support static use without its start-up code.
- **Link through `cc`, or with musl.** New tooling; the human has not
  ruled on it.
- **Always link with the C library.** Every program would need the
  loader and glibc's development files, and existing executables would
  change for no gain.
- **Let lowering list the C symbols it calls.** The object file already
  says, and reading it cannot miss a symbol that a lowering forgot.

## Consequences

- A host that builds such a program needs glibc's development files
  (`libc.so`; Debian's and Ubuntu's `libc6-dev`), and the executable runs
  only where that loader and glibc are.
- A symbol that no library defines is a `tool-error` from `ld`.
- The table's stack figure counts nothing for a C function's own frames,
  only the runtime's 16 KiB. #239, which adds calls to C, decides what a
  C callee's stack counts.
