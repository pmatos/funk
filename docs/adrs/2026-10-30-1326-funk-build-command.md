# funk build writes OUTPUT.o and OUTPUT all or nothing, and adds the verdicts unsupported and tool-error

Status: accepted

## Context

[#12](https://github.com/pmatos/funk/issues/12) adds `funk build`, the
driver's command for the x86-64 backend. ADR-2026-10-30-1032 says how funk
reports: one verdict per file, as text or as JSON lines, with the verdicts
`accepted`, `parse-error`, `validation-error` and `io-error`; a new verdict
takes a new ADR. A valid module can hold parts that the backend cannot
lower yet. The build runs GNU `as` and `ld` (ADR-2026-10-30-1229), which can
be missing, fail or warn.

## Decision

- **Command.** `funk build [--json] -o OUTPUT FILE` reads, parses and
  validates `FILE` (`-` is standard input), lowers it, and writes the
  object file `OUTPUT.o` and the executable `OUTPUT`, which runs one
  function (ADR-2026-10-30-1233). `OUTPUT` is a path even when it reads as
  a flag, such as `-h`. The command prints nothing when it succeeds. With
  `--json`, its one report line adds two fields, `object` and
  `executable`, the paths it wrote.
- **All or nothing.** The build writes every file to a new hidden directory
  next to `OUTPUT`, then moves `OUTPUT.o` and then `OUTPUT` into place,
  only once both are built. A build that fails leaves both paths as they
  were. The one exception: if `OUTPUT` cannot be moved into place, the new
  `OUTPUT.o` is removed again.
- **`unsupported`**, a new verdict and kind: the module is valid, but the
  backend cannot lower part of it. Every such part is reported, in one
  pass. Each diagnostic has the fields of a validation error (`func`,
  `block`, `op`, `loc`), and the text form is
  `FILE: unsupported in @f ^block op N: MESSAGE (at @R = LOCATION)`.
- **`tool-error`**, a new verdict and kind: `as` or `ld` could not run,
  failed, or printed anything. Its message holds the tool's output, and the
  text form is `FILE: error: MESSAGE`.
- **`io-error`** keeps its meaning: funk could not read `FILE`, create the
  hidden directory, or write or move an output. An output that would
  overwrite `FILE` is one too.
- **Other verdicts.** A module that does not parse or validate gets the
  verdict that `funk verify` gives it.
- **Exit status.** 0 when built; 1 on `parse-error`, `validation-error` or
  `unsupported`; 2 on a usage error, `io-error` or `tool-error`.

## Alternatives

- **Report what the backend cannot lower as a validation error.** The
  module is valid by the spec, and #13 compares `funk verify`'s verdict
  with `fir-ref`'s, which must not change as the backend grows.
- **Let `as` and `ld` write the outputs in place.** Simpler, but a tool that
  warns or fails after it wrote leaves an output of a failed build, and a
  script that looks for the file, not the exit status, runs it.
- **The hidden directory in the system's temporary directory.** That is
  often another file system, where a rename cannot move a file.

## Consequences

- #13 can tell a part that the backend cannot lower yet (status 1) from a
  broken toolchain (status 2).
- A failed build never replaces a working `OUTPUT` or `OUTPUT.o`.
- A build that is killed can leave a hidden `.funk-build.PID.N` directory
  next to `OUTPUT`.
- `unsupported` shrinks as op families land; each lowering reports, at its
  op, what it does not handle.
