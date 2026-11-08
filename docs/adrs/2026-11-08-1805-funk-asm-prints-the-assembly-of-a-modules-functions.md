# `funk asm` prints the assembly of a module's functions

Status: accepted

## Context

`funk build` writes only an object file and an executable. The fir explorer
([#216](https://github.com/pmatos/funk/issues/216)) has to show what funk
generates. Disassembling the object file would lose what the backend knows:
each op's comment, the labels of the blocks and the directives. The backend
already produces this text in `funk_x86_64::compile`.

## Decision

- `funk asm [--json] FILE` parses, validates and lowers one file, as
  `funk build` does, and writes no file.
- It prints the module's assembly, `Program.module`, on standard output.
  With `--json`, the report of ADR-2026-10-30-1032 holds it as `text`.
- It leaves out `Program.entry`, the runtime and the wrappers that run a
  function from the command line. They are the same for every module and say
  nothing about how its ops were lowered.
- Its verdicts and exit statuses are those of `funk build`
  (ADR-2026-10-30-1326). A module that the backend cannot lower is
  `unsupported`, with located diagnostics.

## Alternatives

- **Run `objdump` on the object file.** It needs no change to funk, but it
  drops the comment that ties each instruction to its op.
- **Add `-S` to `funk build`.** A build needs an output path and runs `as`
  and `ld`, and printing the assembly needs neither.

## Consequences

- The assembly's comments become visible to users. Its text is not a stable
  interface, and the explorer only reads the comment before each op.
