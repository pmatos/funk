# Current decisions: the funk command

This page continues [rust-ir-and-tools.md](rust-ir-and-tools.md). It says what
the `funk` command does: its commands, verdicts and exit statuses, its report,
and how it uses its standard streams. These are rules of one crate, `funk`, so
they have no ADR. The harness and `fir-ref` read the verdicts and the JSON
report, so this page is that interface's record (ADR-2026-11-09-1610).

## Commands and verdicts

funk has four commands: `funk fmt [--check | --write] [--json] FILE...`,
`funk verify [--json] FILE...`, `funk build [--json] -o OUTPUT FILE` and
`funk asm [--json] FILE`. `fmt` parses and prints, and does not validate: every
module that parses has a canonical form, since the printer is the formatter
(ADR-2026-10-29-2014). `verify` parses and validates. `build` also lowers and
writes outputs. `asm` lowers and writes no file. For `fmt`, `verify` and
`build`, `-` is standard input.

Each file gets one verdict: `accepted`, `parse-error`, `validation-error` or
`io-error`. `build` and `asm` add `unsupported` and `tool-error`.

`fmt` and `verify` exit with 0 when every file is accepted, and canonical under
`--check`. They exit with 1 when one is rejected, or not canonical under
`--check`. They exit with 2 on a usage or I/O error. With several files, the
status is the largest.

`build` and `asm` exit with 0 on success. They exit with 1 on `parse-error`,
`validation-error` or `unsupported`. They exit with 2 on a usage error,
`io-error` or `tool-error`. So the harness can tell a part that the backend
cannot lower yet (1) from a broken toolchain (2).

When funk cannot write its output, it says so on standard error and exits with
status 2. A closed pipe, as `head` leaves, ends it with 2 and no message.

## Report format

Text diagnostics go to standard error, one per line. A parse error is
`FILE:LINE:COL: parse error: REASON`. A validation error is
`FILE: validation error in @f ^block op N: MESSAGE (at @R = LOCATION)`, with the
parts that apply. Symbols and strings appear in their canonical spelling, so a
diagnostic never spans lines or holds a hidden character.

With `--json`, each file gets one JSON object on one line of standard output. It
has `file`, `verdict` and `diagnostics`. A diagnostic has a `kind`, the verdict
it gives, and a `message`. A parse error adds `line` and `column`, in UTF-8
bytes from 1. A validation error adds `func`, `block`, `op`, the index in its
block, and `loc`, each `null` when it does not apply. `loc` is
`{"ref": N, "location": "..."}`, with the location as the table prints it, or
`null` when the table lacks the reference. Strings escape, as `\uXXXX`, every
character that a fir string escapes.

`fmt` adds `canonical`, and without `--check` or `--write` the canonical `text`.
`build` adds `object` and `executable`, the paths it wrote. `asm` holds the
assembly in `text`.

The parser stops at its first error. The verifier reports every rule the module
breaks, so an agent gets every validation error in one run. The spec does not
say which error of a text with several comes first. funk reports the first
error of the earliest phase: characters and tokens, then the grammar, then
decoding, which checks each function's definitions before its ops. Another
parser may report another of the errors.

Messages are for people. Tools compare verdicts and kinds, never message text.
They compare positions only for a text with one error. A new field does not
break readers. Renaming a field or a verdict breaks them: the PR that does it
changes this section, `fir-ref`'s report and the harness together, and says so.

## funk fmt

`--check` lists the files that are not canonical, and `--write` rewrites them.
The printer never holds the whole canonical text, which for nested regions grows
with the square of their depth (#51). `funk_ir::text::write_module` writes a
module's text to any `fmt::Write`, piece by piece. It stops at the sink's first
error. `print`, `print_op` and `print_func` wrap it and return a `String`.

`--check` compares as it prints, and fails at the first piece that differs.
`--write` first checks the file the same way, so a canonical file is left alone.
It then streams into its temporary file. Plain `fmt` streams to standard output.
`fmt --json` gives `canonical` before `text`, so funk checks the file, then
prints the text a second time. Memory is linear in the input, and
`crates/funk/tests/fmt_check_memory.rs` gets a verdict with 256 MiB of data.

`--write` writes a new file next to the old one, readable only by its owner,
under an unused name. It gives that file the old file's permissions, then renames
it over the old one. A failed write leaves the file as it was, and nothing that
already exists is opened or removed. funk refuses, as an I/O error, a file it
may not write and anything but a regular file. The new file has funk's owner and
group, and loses the old file's ACLs and extended attributes; another hard link
to the old file keeps the old text.

## funk build

`funk build` reads, parses and validates `FILE`, then lowers it. It writes the
object file `OUTPUT.o` and the executable `OUTPUT`. The executable runs one
function (ADR-2026-10-30-1233). `OUTPUT` is a path even when it reads as a flag,
such as `-h`. The command prints nothing when it succeeds.

The build is all or nothing. It writes every file to a new hidden directory next
to `OUTPUT`. It moves `OUTPUT.o` and then `OUTPUT` into place, only once both are
built. A failed build leaves both paths as they were. The one exception: if
`OUTPUT` cannot be moved into place, the new `OUTPUT.o` is removed again. A build
that is killed can leave a hidden `.funk-build.PID.N` directory. Rejected:
letting `as` and `ld` write the outputs in place, since a tool that fails after
writing leaves an output of a failed build; and the hidden directory in the
system's temporary directory, often another file system, where a rename cannot
move a file.

`unsupported` means the module is valid but the backend cannot lower part of it.
Every such part is reported in one pass, with the fields of a validation error,
and the text form is
`FILE: unsupported in @f ^block op N: MESSAGE (at @R = LOCATION)`. Rejected:
reporting it as a validation error, since the module is valid by the spec and
`funk verify`'s verdict, which the harness compares with `fir-ref`'s, must not
change as the backend grows.

`tool-error` means `as` or `ld` could not run, failed or printed anything. Its
message holds the tool's output, and its text form is `FILE: error: MESSAGE`.

`io-error` means funk could not read `FILE`, create the hidden directory, or
write or move an output. An output that would overwrite `FILE` is one too. A
module that does not parse or validate gets the verdict `funk verify` gives it.

## funk asm

`funk asm` parses, validates and lowers one file, as `funk build` does, and
writes no file. It prints the module's assembly, `Program.module`, on standard
output, with each op's comment, the blocks' labels and the directives; the fir
explorer reads the comment before each op (#216). It leaves out
`Program.entry`, the runtime and the wrappers that run a function from the
command line, which are the same for every module. Its verdicts and exit
statuses are those of `funk build`. The assembly's text is not a stable
interface. Rejected: `objdump` on the object file, which drops the comment that
ties each instruction to its op; and `-S` on `funk build`, which needs an output
path and runs `as` and `ld`.

## Standard streams

On Unix, funk reaches its standard streams only through
`crates/funk/src/streams.rs`. It uses a `File` on a duplicate of descriptor 0,
1 or 2, made by `try_clone_to_owned`, which is safe code. The reason is that
the standard library's handles take `EBADF` for the end of the input and for a
successful write, and a descriptor open in the wrong mode gives `EBADF` (#104).
New input and output goes through `streams`. Rejected: checking each
descriptor's mode with `fcntl(F_GETFL)`, which needs unsafe code or a
third-party crate.

Standard output is a `LineWriter`, and standard error is not buffered, as the
standard library's are. A test checks that the lines of both come in order on
one file. Rejected: a `BufWriter`, which would change how the two interleave.
funk holds up to three more descriptors, so under an open-file limit below 6 it
reports "Too many open files"; `fir-ref` fails below 12.

A stream that was closed at start-up is `/dev/null` (ADR-2026-11-09-1603).
Before `main`, Rust's standard library opens `/dev/null` on each of descriptors
0 to 2 that is closed, and funk does not look behind that. A closed standard
input reads as an empty text, so `-` is a parse error with exit 1. A closed
standard output or standard error takes funk's writes, and funk exits with its
verdict. `fir-ref` exits with 2 when it needs a closed stream, so the two tools
differ here. The harness never closes a standard stream, so it never compares
them.

A standard input funk cannot read is `cannot read standard input: ...`, an
`io-error` with exit 2. A standard output it cannot write ends the run with
`funk: cannot write standard output: ...` on standard error and exit 2. A
diagnostic it cannot write to standard error ends the run with exit 2 and no
message. A run that writes nothing to a stream it cannot use exits as usual, as
`fir-ref` does.

Off Unix, funk keeps the standard library's handles: on Windows they write to a
console as UTF-16, which a `File` would not do. A panic still prints through
the standard library's standard error, and exits with 2.
