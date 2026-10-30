# funk build writes AT&T assembly and runs GNU as and ld

Status: accepted

## Context

The roadmap leaves to an ADR whether the backend emits assembly or ELF
directly. `funk build` must write an object file and an executable
([#12](https://github.com/pmatos/funk/issues/12)). The M0 backend is naive,
and its output is checked by running it, against `fir-ref`. Rust's own
toolchain needs a system linker on Linux, so a machine that builds funk
already has one. M5 (JIT) will need machine code in memory, so an encoder
of its own will come later.

## Decision

- **Assembly text.** The backend writes GNU `as` assembly in AT&T syntax,
  as plain text. AT&T syntax writes every register with `%`, so no symbol
  reads as a register, whatever its name; in Intel syntax a function named
  `rax`, `byte` or `offset` would.
- **Two assembly files.** One holds the module's functions; it becomes the
  object file. The other holds the entry point of the executable and its
  runtime (ADR-2026-10-30-1233). Both end with the section
  `.note.GNU-stack`, so the stack is not executable.
- **GNU binutils assemble and link.** `as --64` assembles each file.
  `ld -m elf_x86_64 -static` links the module's object and the entry's
  object into a static executable with the entry point `__funk_start`.
  Both are told the target, so neither a tool's configured default nor
  `LDEMULATION` changes what they build. There is no libc, no C compiler
  and no dynamic linker.
- **Outputs.** `funk build -o OUTPUT FILE` writes the object file
  `OUTPUT.o` and the executable `OUTPUT`. The assembly files and the
  entry's object go to a temporary directory, which funk removes;
  ADR-2026-10-30-1326 says how the outputs are moved into place.
- **A tool that prints is a tool that failed.** If `as` or `ld` cannot run,
  exits with an error, or prints anything, such as a warning, the build
  fails with the tool's words (a `tool-error`).
- **Setup and CI.** `scripts/ensure-hooks.sh` warns unless the host is
  x86-64 Linux and `as` and `ld` are GNU binutils'. The CI job installs
  `binutils` when its runner lacks `as` or `ld`.

## Alternatives

- **Write ELF directly**: encode instructions and write object files and
  executables in Rust. No external tools, but an encoder and an ELF writer
  to write and test first, and no readable output. M5 needs an encoder;
  this text output will be its oracle.
- **Intel syntax.** Closer to the vendor manuals, but symbols can clash
  with register and operator names, as above.
- **Link with libc through `cc`.** The entry point could be C, but funk
  would need a C compiler and libc, and the executable would depend on
  them.

## Consequences

- `funk build` needs GNU `as` and `ld` (binutils) on `PATH` on an x86-64
  Linux host.
- The assembly is readable, so a person or an agent can inspect what the
  backend wrote; `funk_x86_64::compile` returns it.
- Each build starts two processes of `as` and one of `ld`.
- binutils is not pinned, unlike Rust (ADR-2026-10-30-1030) and Lean
  (ADR-2026-10-29-2135). CI takes it from the `ubuntu-26.04` image, and its
  log shows both versions; a machine uses its distribution's. Since a tool
  that prints fails the build, a binutils release that adds a warning, as
  2.39 did for executable stacks, fails `funk build` until the backend's
  output avoids it, and a local pass may not predict CI's. Pinning
  (`apt-get install binutils=VERSION`) is the remedy if that happens
  often.
