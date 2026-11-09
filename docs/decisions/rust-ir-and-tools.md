# Current decisions: the Rust IR and tools

This page says what holds today for funk's Rust IR and tools. It summarizes
the ADRs it cites and replaces none of them. When this page and an ADR
disagree, the page has the bug (ADR-2026-11-09-1610).

## Workspace and toolchain

funk's Rust code is one virtual Cargo workspace (ADR-2026-10-30-1030). Every
crate of the workspace sits under `crates/`. The library `funk-ir` holds the
IR, op registry, builder, parser, printer, verifier and module generator. The
crate `funk` is the binary. `funk-start-fds` holds the start-up constructor
(ADR-2026-11-02-2253). `funk-x86-64` is the backend (ADR-2026-10-30-1228).

The workspace uses edition 2024 and resolver 3. Shared package fields and lints
live in `[workspace.package]` and `[workspace.lints]`. `Cargo.lock` is
committed. The fir texts that the Lean side and the harness share live in
`tests/fir/`, outside the crates. `funk-ir` has one module per layer: `ir`,
`registry`, `dialects`, `text`, `verify` and `generate`.

Inside the workspace, the only third-party dependency is vstd, on
`funk-start-fds` alone, with the crates vstd brings (ADR-2026-11-03-0809). JSON
output, argument parsing, big integers and the generator's random numbers are
small modules of funk's own (ADR-2026-10-30-1030).

`rust-toolchain.toml` is the one pin. It names an exact stable release, with
the `minimal` profile and the `rustfmt` and `clippy` components. `rust-version`
in the workspace is the pin's minor release. The workspace uses no nightly and
no floating `stable`. A bump is one PR. It changes the pin, fixes what the new
lints find and passes every check.

The fuzz targets are the exception, and they are outside the workspace. `fuzz/`
is a crate of its own that runs on a pinned nightly, because `cargo-fuzz` needs
one (ADR-2026-11-08-2117).

Three hooks check the Rust code: `rust-fmt`, `rust-clippy` and `rust-test`.
Clippy runs with `-D warnings`, and rustfmt uses its default style. Each hook
calls `scripts/check-rust.sh`. That script ignores `RUSTUP_TOOLCHAIN`. It fails
when the cargo or rustc on `PATH` is not the pinned release. Every commit that
touches Rust runs the whole test suite, so the tests must stay fast
(ADR-2026-10-30-1030).

In CI these hooks run in the `rust` job, "Rust suite". It is one of the suite
jobs behind the required gate job `pre-commit` (ADR-2026-11-05-1408). The same
job runs `verus-proof`, `verus-report-test`, `unsafe-code` and
`unsafe-code-test`. It installs rustup, the pinned Rust toolchain, Verus and GNU
binutils.

`scripts/ci-install.sh` runs each installer step. It downloads `rustup-init` or
the Verus zip only on a cache miss. It checks the file against the SHA-256
written in the workflow on every run (ADR-2026-11-05-1954).
`scripts/ensure-hooks.sh` warns when cargo is missing (ADR-2026-10-30-1030).

## The IR and the op registry

An op is generic data, checked through a registry of dialects
(ADR-2026-10-30-1146). There is no closed `enum` of core ops. `funk_ir::Op` has,
in the spec's order, `results`, `name`, `attrs`, `operands`, `succs`, `regions`
and `loc`. The name is a string. Attributes and types are generic terms, as the
text writes them. `loc` is a `LocRef`, not an `Option`, so no op exists without
a location.

`Item` follows the spec. Today it has one variant, `Func`, and is
`#[non_exhaustive]`. The M1 design registers more kinds of item
(ADR-2026-11-09-1543), and `funk-ir` does not implement that yet. A module is
the symbol table of its own items.

A `Dialect` gives `OpSpec`s, one per op name, and `TypeSpec`s. `OpSpec::decode`
takes an op's attributes and the types of its operands and results. It returns
the op's `OpShape`, or why the op does not decode. `OpSpec::check` is the
dialect's own rule. `TypeSpec::check` says whether a type decodes and whether it
is valid. Registering rejects an op name that is not a word or is already
registered.

No per-op code exists outside the dialect. The parser reads the one grammar,
then decodes each op and type through the registry. A failure there is a parse
error. The printer writes every op the same way. The verifier looks up operand
types and calls the same `decode`. So an op that a builder or a pass made
ill-typed is a validation error. Checks such as an op's operand count live in
each op's `decode`. An op that the registry lacks is a parse error in `funk`,
and corpus texts use only registered ops (ADR-2026-10-30-1146).

Generic code must not know the ops of any dialect (ADR-2026-11-03-0600). In
Rust, that is all of `funk-ir`'s `src/` except `src/dialects/`, the module
generator and unit tests. Code that builds, lowers or runs one dialect's
programs may name its ops. That covers the dialect's files, the generator, the
x86-64 backend, `funk`'s command line and the tests. `crates/funk-ir/tests/g0.rs`
keeps this line in `rust-test`. A word that names a core op counts as a core
word in generic code, whatever else it means (ADR-2026-11-03-1617).

The core dialect is `dialects/core/`. Each op family has a file of its own,
registered in `dialects/core/mod.rs`. A new dialect implements `OpSpec` and
`TypeSpec` and registers. The IR, parser, printer and verifier then do not
change.

A test-only dialect names its ops and types `toy.` and a word, such as `toy.br`.
A sum of the core and a test dialect routes each `toy.` name to the test
dialect. Every other name goes to the core (ADR-2026-10-30-1146). H4 makes this
the general rule. Every dialect but the core writes its ops, types and attributes
as `name.word`, and test dialects keep `toy.` (ADR-2026-11-09-1543). That design
is in semantics-m1-design.md, and `funk-ir` does not implement it yet.

### Nesting

fir has no nesting limit, and every tool handles any depth on a small stack
(ADR-2026-10-30-1549). In `funk-ir`, nothing recurses once per level of nesting
(ADR-2026-10-30-1333). Each level costs constant native stack, and the path from
the root lives in a `Vec` on the heap. `ir/tree.rs` holds the helpers that walk,
compare, hash, build and drop trees.

`Attr` and `Region` write `Clone`, `PartialEq`, `Eq`, `Hash`, `Debug` and `Drop`
with these helpers. `Type`, `Block`, `Op`, `Func`, `Item` and `Module` keep their
derives.

`funk` runs on its main thread, with no large reserved stack. A panic exits with
status 2. `tests/deep.rs` runs on 256 KiB threads, mostly a million levels deep.
`funk verify` and `funk fmt` give their verdicts on such files with a 1 MiB
stack.

Since `Attr` and `Region` implement `Drop`, code cannot move a field out of an
owned one. It borrows, clones or uses `std::mem::take`. Code in `funk-ir` walks
with `walk` or `Region::parts`. Other crates walk the public fields with an
explicit stack of their own. A walk that recurses once per level is a bug
anywhere. Memory bounds depth, not the stack (ADR-2026-10-30-1333).

### Constants near a width's limit

A core `const` must fit its type, and a width goes up to 16,777,215 bits
(ADR-2026-11-03-1000). `funk-ir` holds a constant as its decimal spelling.
`Int::fits_signed` decides most digit counts from bounds on log2(10). When the
count does not decide, it computes `2^(w-1)` in decimal and compares it with the
magnitude. The digits are never converted to binary (ADR-2026-10-30-1218).

`2^k` is built by squaring and doubling, in base-10^5 limbs, in
`crates/funk-ir/src/ir/int/decimal.rs`. Squaring uses an NTT over
`2^64 - 2^32 + 1`, in `ir/int/ntt.rs`, with no `unsafe`. Every `u32` width is
exact, and an `assert!` guards the bound. Correctness rests on tests against the
quadratic code and on the coefficient bound. A change of base must recheck that
bound.

## Unsafe code and Verus

Unsafe Rust lives only in a verified module, whose trusted base is listed
(ADR-2026-11-03-0808). The module must be in a crate with
`[package.metadata.verus] verify = true`. There is one verified module,
`crates/funk-start-fds/src/record.rs`. Its code is inside `verus!`, except the
trusted pieces that Verus cannot take.

Verus proves `record`, the constructor. When it returns, slot `fd` of `CLOSED`
holds the OS error that `fcntl(fd, F_GETFD)` failed with, for `fd` in 0 to 2.
The slot holds 0 when the call did not fail with one. Every index is in bounds
and nothing panics. Verus checks the module on x86-64 Linux, in CI.

The trusted base is listed in ADR-2026-11-03-0808 and marked TRUSTED in the
code. It is the `fcntl` extern block, `getfd`, `Slots`, `store`, `take_slots`,
the `RECORD` static and the module's `#![allow(unsafe_code)]`.

`scripts/unsafe_pins.py` keeps a digest of the trusted base, of the #117
specification and of `record`. The check fails when a pinned text changes. Only
`record_slots`' body and new items inside `verus!` change without a new pin.
Verus checks both. `record_slots` may gain helpers inside `verus!` without a new
ADR.

Changing a pinned text, or adding a verified module, needs a new ADR and a human
ruling. That ADR restates every digest. `ADR` in `scripts/check_unsafe_code.py`
then points at it.

`scripts/check_unsafe_code.py` reads every tracked Rust file and manifest by
tokens. It catches careless or well-meaning changes. Review of the diff is the
defence against a deliberately disguised change. The check over-approximates, so
a name that it flags is renamed.

In every crate, `unsafe` appears only on a trusted item. `unsafe_code` appears in
an attribute only inside `forbid(...)` or `deny(...)`, besides the trusted one.
`[workspace.lints]` keeps `unsafe_code = "forbid"`. A crate with no verified
module inherits it or sets `forbid` itself. Each library root holds
`#![doc(test(attr(forbid(unsafe_code))))]`, because cargo does not pass `[lints]`
to doctests. No identifier starts with `verus_`.

In a crate that uses vstd, words such as `assume`, `admit`, `axiom` and
`external` appear only on a trusted item. So does the one allowed verifier
attribute, `verifier::external_body`.

A crate with a verified module sets `unsafe_code = "deny"` in its own
`[lints.rust]` and has no `extern crate`. Only a verified module uses vstd or
calls `verus!`.

Inside a verified module, only inner attributes, `use`, constants and trusted
items sit outside `verus!`. The module has no other macro call, no `cfg` and no
`use ... as`.

The `verus-proof` hook fails unless Verus proved each function that
`scripts/verus_report.py` names for the crate. `unsafe-code-test` checks that
the ADR names every trusted item and digest.

### The start-up constructor

Rust's start-up code opens `/dev/null` on each closed standard descriptor. Only
code that runs before it can see that a descriptor is closed. The human ruled
for this one scoped exception, to keep funk's verdicts identical to `fir-ref`'s
(ADR-2026-11-02-2253).

`funk-start-fds` puts one function in `.init_array`. It calls
`fcntl(fd, F_GETFD)` on descriptors 0, 1 and 2 and stores the result in atomics.
`closed_at_start(Stream)` returns what it recorded. The constructor is built on
ELF Unix targets only. Elsewhere it compiles out and every descriptor reads as
open. CI tests this on Linux only.

`funk-start-fds` has its own `[lints]`, with `unsafe_code = "deny"` and the
workspace's other lints. A lint added to `[workspace.lints]` is added there too.
That is a convention, not a check (ADR-2026-11-03-0808). Every other crate,
`funk` included, keeps `forbid`. This module is the workspace's only unsafe code.

### The Verus pin

Verus is pinned to one release, and vstd to the exact version it ships
(ADR-2026-11-03-0809). `scripts/check-verus.sh` holds the pin. It fails when
`verus` on `PATH` is another release or runs on another Rust than the pin. It
runs the `cargo-verus` beside that `verus`. `scripts/ensure-hooks.sh` warns when
Verus is missing.

The `verus-proof` hook runs
`cargo verus verify --workspace --locked --check-toolchain`, in `target/verus`.
It verifies every crate that opts in, and vstd. `--check-toolchain` fails when vstd's version is not the release's.
`Cargo.lock` pins what vstd brings.

A bump is one PR. It moves the release and its SHA-256 in the workflow, the pin
in `scripts/check-verus.sh` and vstd's version together. It also moves the Rust
pin when the new release runs on another toolchain. Dependabot watches `cargo`
but ignores vstd and the `verus_*` crates. An advisory against one of those needs
a bump by hand.

## The funk command

### Commands and verdicts

funk has four commands: `funk fmt [--check | --write] [--json] FILE...`,
`funk verify [--json] FILE...`, `funk build [--json] -o OUTPUT FILE` and
`funk asm [--json] FILE`. `fmt` parses and prints, and does not validate.
`verify` parses and validates (ADR-2026-10-30-1032). `build` also lowers and
writes outputs (ADR-2026-10-30-1326). `asm` lowers and writes no file
(ADR-2026-11-08-1805). For `fmt`, `verify` and `build`, `-` is standard input.

Each file gets one verdict: `accepted`, `parse-error`, `validation-error` or
`io-error`. `build` and `asm` add `unsupported` and `tool-error`.

`fmt` and `verify` exit with 0 when every file is accepted, and canonical under
`--check`. They exit with 1 when one is rejected, or not canonical under
`--check`. They exit with 2 on a usage or I/O error. With several files, the
status is the largest (ADR-2026-10-30-1032).

`build` and `asm` exit with 0 on success. They exit with 1 on `parse-error`,
`validation-error` or `unsupported`. They exit with 2 on a usage error,
`io-error` or `tool-error` (ADR-2026-10-30-1326, ADR-2026-11-08-1805).

When funk cannot write its output, it says so on standard error and exits with
status 2. A closed pipe, as `head` leaves, ends it with 2 and no message
(ADR-2026-10-30-1032).

### Report format

Text diagnostics go to standard error, one per line. A parse error is
`FILE:LINE:COL: parse error: REASON`. A validation error is
`FILE: validation error in @f ^block op N: MESSAGE (at @R = LOCATION)`, with the
parts that apply.

With `--json`, each file gets one JSON object on one line of standard output. It
has `file`, `verdict` and `diagnostics`. A diagnostic has a `kind` and a
`message`. A parse error adds `line` and `column`, in UTF-8 bytes from 1. A
validation error adds `func`, `block`, `op` and `loc`, each `null` when it does
not apply. `loc` is `{"ref": N, "location": "..."}`, or `null` when the table
lacks the reference.

`fmt` adds `canonical`, and without `--check` or `--write` the canonical `text`.
`build` adds `object` and `executable`. `asm` holds the assembly in `text`.

The parser stops at its first error. The verifier reports every rule the module
breaks. funk reports the first error of the earliest phase: characters and
tokens, then the grammar, then decoding. Another parser may report another of
the errors.

Messages are for people. Tools compare verdicts and kinds, never message text.
They compare positions only for a text with one error. A new field does not break
readers. Renaming a field or a verdict takes a new ADR (ADR-2026-10-30-1032).

### funk fmt

`--check` lists the files that are not canonical, and `--write` rewrites them.
The printer never holds the whole canonical text (ADR-2026-11-05-1713).
`funk_ir::text::write_module` writes a module's text to any `fmt::Write`, piece
by piece. It stops at the sink's first error.

`--check` compares as it prints, and fails at the first piece that differs.
`--write` first checks the file the same way, so a canonical file is left alone.
It then streams into its temporary file. Plain `fmt` streams to standard output.
`fmt --json` gives `canonical` before `text`, so funk checks the file, then
prints the text a second time. Memory is linear in the input.

`--write` writes a new file next to the old one, readable only by its owner,
under an unused name. It gives that file the old file's permissions, then renames
it over the old one. A failed write leaves the file as it was. funk refuses, as
an I/O error, a file it may not write and anything but a regular file
(ADR-2026-10-30-1032).

### funk build

`funk build` reads, parses and validates `FILE`, then lowers it. It writes the
object file `OUTPUT.o` and the executable `OUTPUT` (ADR-2026-10-30-1326). The
executable runs one function (ADR-2026-10-30-1233). The command prints nothing
when it succeeds.

The build is all or nothing. It writes every file to a new hidden directory next
to `OUTPUT`. It moves `OUTPUT.o` and then `OUTPUT` into place, only once both are
built. A failed build leaves both paths as they were. The one exception: if
`OUTPUT` cannot be moved into place, the new `OUTPUT.o` is removed again.

`unsupported` means the module is valid but the backend cannot lower part of it.
Every such part is reported in one pass, with the fields of a validation error.
It is not a validation error, because `funk verify`'s verdict must not change as
the backend grows.

`tool-error` means `as` or `ld` could not run, failed or printed anything. Its
message holds the tool's output, and its text form is `FILE: error: MESSAGE`.

`io-error` means funk could not read `FILE`, create the hidden directory, or
write or move an output. An output that would overwrite `FILE` is one too. A
module that does not parse or validate gets the verdict `funk verify` gives it.

### funk asm

`funk asm` parses, validates and lowers one file, as `funk build` does, and
writes no file (ADR-2026-11-08-1805). It prints the module's assembly,
`Program.module`, on standard output. It leaves out `Program.entry`, the runtime
and the wrappers that run a function from the command line. The assembly's text
is not a stable interface.

### Standard streams

On Unix, funk reaches its standard streams only through
`crates/funk/src/streams.rs` (ADR-2026-11-03-0107). It uses a `File` on a
duplicate of descriptor 0, 1 or 2, made by `try_clone_to_owned`. The reason is
that the standard library's handles hide `EBADF`. New input and output goes
through `streams`.

Standard output is a `LineWriter`, and standard error is not buffered. A stream
that `funk-start-fds` records as closed fails every read and write with `EBADF`.
That covers standard input, standard output and standard error.

A standard input funk cannot read is `cannot read standard input: ...`, an
`io-error` with exit 2. A standard output it cannot write ends the run with
`funk: cannot write standard output: ...` on standard error and exit 2. A
diagnostic it cannot write to standard error ends the run with exit 2 and no
message. A run that writes nothing to a stream it cannot use exits as usual, as
`fir-ref` does.

Off Unix, funk keeps the standard library's handles. A panic still prints through
the standard library's standard error, and exits with 2.

## Other tools

testing-and-harness.md describes the fir explorer. Its native runs keep the
harness's data limit (ADR-2026-11-08-1806).
