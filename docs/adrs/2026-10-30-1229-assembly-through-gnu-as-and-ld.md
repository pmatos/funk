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
- **GNU binutils assemble and link.** `as --64` assembles each file. `ld`
  links the module's object and the entry's object into a static
  executable with the entry point `__funk_start`. There is no libc, no C
  compiler and no dynamic linker.
- **Outputs.** `funk build -o OUTPUT FILE` writes the object file
  `OUTPUT.o` and the executable `OUTPUT`. The assembly files and the
  entry's object go to a temporary directory, which funk removes.
- **A tool that prints is a tool that failed.** If `as` or `ld` cannot run,
  exits with an error, or prints anything, such as a warning, the build
  fails with the tool's words (a `tool-error`).
- **Setup and CI.** `scripts/ensure-hooks.sh` warns when `as` or `ld` is
  missing. The CI job installs `binutils` when its runner lacks `as` or
  `ld`.

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
