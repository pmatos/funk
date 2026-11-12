# Current decisions: the Rust IR and tools

This page says what holds today for funk's Rust workspace, its IR and op
registry, its unsafe-code rule and its speed guard.
[rust-ir-and-tools-funk.md](rust-ir-and-tools-funk.md) continues it with the
`funk` command. The pages are the record: when a page and an ADR disagree, the
page wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610).

## Workspace and toolchain

funk's Rust code is one virtual Cargo workspace (ADR-2026-10-30-1030). Every
crate of the workspace sits under `crates/`. The library `funk-ir` holds the
IR, op registry, builder, parser, printer, verifier and module generator. The
crate `funk` is the binary. `funk-x86-64` is the backend
(ADR-2026-10-30-1228).

The workspace uses edition 2024 and resolver 3. Shared package fields and lints
live in `[workspace.package]` and `[workspace.lints]`. `Cargo.lock` is
committed. The fir texts that the Lean side and the harness share live in
`tests/fir/`, outside the crates. `funk-ir` has one module per layer: `ir`,
`registry`, `dialects`, `text`, `verify` and `generate`.

The workspace depends on no third-party crates (ADR-2026-11-09-1603). JSON
output, argument parsing, big integers and the generator's random numbers are
small modules of funk's own (ADR-2026-10-30-1030). Dependabot already watches
the `cargo` ecosystem, so the first dependency gets its updates.

`rust-toolchain.toml` is the one pin. It names an exact stable release, with
the `minimal` profile and the `rustfmt` and `clippy` components. `rust-version`
in the workspace is the pin's minor release. The workspace uses no nightly and
no floating `stable`. A bump is one PR. It changes the pin, fixes what the new
lints find and passes every check.

Rejected: a floating `stable` channel, since a new release's lints could turn
CI red with no change in the repository; and `proptest`, `serde_json` and
`clap`, since funk needs little of each and every dependency brings
supply-chain risk and lockfile churn.

The fuzz targets are the exception, and they are outside the workspace. `fuzz/`
is a crate of its own that runs on a pinned nightly, because `cargo-fuzz` needs
one ([testing-and-harness-generated.md](testing-and-harness-generated.md#fuzzing)).

Three hooks check the Rust code: `rust-fmt` (`cargo fmt --all --check`),
`rust-clippy` (`cargo clippy --workspace --all-targets --locked -- -D
warnings`) and `rust-test` (`cargo test --workspace --locked`). rustfmt uses its
default style. Each hook calls `scripts/check-rust.sh`. That script ignores
`RUSTUP_TOOLCHAIN`. It fails when the cargo or rustc on `PATH` is not the
pinned release. The hooks run when a file under `crates/`, a Cargo file, the pin
or the script changes, and `rust-test` also when a file under `tests/fir/`
changes. Every commit that touches Rust runs the whole test suite, so the tests
must stay fast (ADR-2026-10-30-1030).

In CI these hooks run in the `rust` job, "Rust suite". It is one of the suite
jobs behind the required gate job `pre-commit` (ADR-2026-11-05-1408). It
installs rustup, the pinned Rust toolchain, GNU binutils and valgrind.

`scripts/ci-install.sh` runs each installer step. It downloads `rustup-init`
only on a cache miss. It checks the file against the SHA-256 written in the
workflow on every run
([process-ci.md](process-ci.md#installer-downloads)). It installs rustup with
no default toolchain, then `rustup toolchain install` installs what
`rust-toolchain.toml` names. The job caches `~/.rustup/toolchains`, keyed on
`rust-toolchain.toml`, except the runner's own `stable-*`. Rejected:
`dtolnay/rust-toolchain` or another action, since a checksummed `rustup-init`
needs no third-party action. `scripts/ensure-hooks.sh` warns when cargo is
missing (ADR-2026-10-30-1030).

### The speed guard

The `rust-speed` hook counts funk's instructions under cachegrind and compares
them with `scripts/rust-speed-baseline.json` (ADR-2026-11-09-1645). It builds
the release `funk` and generates two large inputs. It runs `funk fmt --check`,
`funk verify` and `funk build` on each. A count fails when it is more than 10%
above the baseline. The human ruled this guard on 2026-11-09 (#174): a check
that counts instructions, fails a PR more than about 10% over a baseline
recorded on `main`, and asks for no speed work yet.

CI is the authority. The baseline comes from CI on `ubuntu-26.04`, and only a
run in CI can fail. Counts depend on the host's glibc and valgrind, so elsewhere
the hook prints the same table and passes. For this hook, a local pass does not
predict a CI pass.

A PR may raise the baseline only by saying so, with the old and new numbers in
its body; the human's ruling asks for this. The numbers to commit are the
`measured` column of CI's table. The start of M2 decides absolute targets for
each op.

Rejected: wall time or a CPU-time limit, since both move with the host and its
load; and failing on every host, since no limit holds for every host's glibc
and valgrind.

## The IR and the op registry

An op is generic data, checked through a registry of dialects
(ADR-2026-10-30-1146). There is no closed `enum` of core ops: G0, which the
human set on 2026-10-29 (ADR-2026-10-29-2016), rules one out. `funk_ir::Op`
has, in the spec's order, `results`, `name`, `attrs`, `operands`, `succs`,
`regions` and `loc`. The name is a string. Attributes and types are generic
terms, as the text writes them. `loc` is a `LocRef`, not an `Option`, so no op
exists without a location. Rejected: a decoded op instance stored in each op,
such as a trait object, since operand and result types would be held twice and
could disagree.

`Item` follows the spec and is `#[non_exhaustive]`: `Func`, `Module` for a
nested module (ADR-2026-11-10-1510), and `Dialect` for an item of a kind
that a dialect registers (ADR-2026-11-10-2224). A dialect registers such a
kind with `Dialect::item_kind` and an `ItemKindSpec`, whose `check` is the
kind's rule; registration puts the kind under the dialect's prefix and
rejects a kind of the core. A module is the symbol table of its own items.

A `Dialect` gives `OpSpec`s, one per op name, and `TypeSpec`s. `OpSpec::decode`
takes an op's attributes and the types of its operands and results. It returns
the op's `OpShape`, or why the op does not decode. `OpSpec::check` is the
dialect's own rule. `OpSpec::effects`, which every op must give, is its set of
effects; each core op's equals its Lean set (semantics-effects.md,
ADR-2026-11-09-1541). `OpSpec::callee` names the function an op calls, `None`
by default, and `Summaries` gives each function of a table the effects that
a call of it may have (ADR-2026-11-10-2108).
`TypeSpec::check` says whether a type decodes and whether it
is valid. Registering rejects an op name that is not a word or is already
registered, and a failed registration changes nothing (ADR-2026-10-30-1146).

No per-op code exists outside the dialect. The parser reads the one grammar,
then decodes each op and type through the registry. A failure there is a parse
error. The printer writes every op the same way. The verifier looks up operand
types and calls the same `decode`. So an op that a builder or a pass made
ill-typed is a validation error. Checks such as an op's operand count live in
each op's `decode`. An op that the registry lacks is a parse error in `funk`,
and corpus texts use only registered ops (ADR-2026-10-30-1146). Types are terms,
not interned or trait objects: a type term has one spelling, so comparing terms
compares types.

Generic code must not know the ops of any dialect (ADR-2026-11-03-0600). In
Rust, that is all of `funk-ir`'s `src/` except `src/dialects/`, the module
generator and unit tests. Code that builds, lowers or runs one dialect's
programs may name its ops. That covers the dialect's files, the generator, the
x86-64 backend, `funk`'s command line and the tests. `crates/funk-ir/tests/g0.rs`
keeps this line in `rust-test`. A word that names a core op counts as a core
word in generic code, whatever else it means (ADR-2026-11-03-1617).

The core dialect is `dialects/core/`. Its types are in `types.rs`, and each op
family has a file of its own, registered in `dialects/core/mod.rs`. A new
dialect implements `OpSpec` and `TypeSpec` and registers. The IR, parser,
printer and verifier then do not change; the test dialect in
`crates/funk-ir/tests/toy.rs` shows it.

### Dialect prefixes

Every dialect but the core writes its ops, types and attributes as `name.word`,
and test dialects are named `toy` (ADR-2026-11-09-1543). The registry routes by
that prefix (ADR-2026-10-30-1146). `word_dialect` in `ir/names.rs` gives the
part of a word before its first `.`, so `toy.a.b` names `toy`, and a bare word
is the core's, the dialect named `dialects::core::NAME`.

A dialect's name is a word with no `.` (`DialectNameNotAPrefix`). Registering
rejects an op that is not written under its dialect's name
(`OpOutsideDialect`), so a core op is bare and a `toy` op is `toy.` and a word,
and one flat map from op names finds each op's dialect. `Registry::check_type`
asks only the `TypeSpec`s of the dialect that a type's head word names, so no
dialect can claim another's type, and a type of an unregistered dialect does
not decode. Rejected: a `TypeSpec` that lists the head words it decodes, since
the core's `iN` is an infinite family; and a map per dialect, looked up after
the prefix, since the flat map gives the same answer with one hash per op on
funk's hot path.

A dialect declares the dialects it depends on with `Dialect::depends_on`: the
dialects whose types its ops may take. Registering rejects a dependency that
is not registered yet (`MissingDependency`), so dependencies form no cycle,
and `Registry::dependencies` gives them back. The core depends on nothing, and
the test dialects depend on the core. A module names its dialect set
([text-format.md](text-format.md#the-dialect-set)), which is to use the
dependencies. Nothing yet checks that a dialect's ops take only types of the
dialects it depends on, or that a module's dialect set holds what its dialects
depend on (ADR-2026-10-30-1146). The rest of the design is in
semantics-m1-design.md.

### Nesting

fir has no nesting limit, and every tool handles any depth on a small stack:
the human ruled so on 2026-10-30 (#36, ADR-2026-10-30-1549). In `funk-ir`,
nothing recurses once per level of nesting. Each level costs constant native
stack, and the path from the root lives in a `Vec` on the heap. Rejected:
growing the stack, with a crate or a new thread every N levels, since it needs
a crate or `unsafe` and derived traits give no place to hook it; and a large
reserved stack, since it moves the overflow deeper but keeps it, and a library
caller does not get it.

`ir/tree.rs` holds the helpers. `walk` gives the `Enter` and `Leave` steps of a
depth-first walk over any `Node`. `equal` and `hash` compare and hash trees from
walks. `Nest` builds a tree top down, with the enclosing lists on a stack.
`drop_all` frees a tree one node at a time. A `Part` is a region, a block or an
op; the printer, the decoder and the traits of `Region` walk parts.

`Attr` and `Region` write `Clone`, `PartialEq`, `Eq`, `Hash`, `Debug` and `Drop`
with these helpers. `Type`, `Block`, `Op`, `Func`, `Item` and `Module` keep their
derives. `Debug` writes, byte for byte, what `#[derive(Debug)]` writes, in every
form, and a test checks it against a derived copy of the types.

The lexer gives one token at a time. Items, regions and the arguments of
attributes are read into a `Nest`. Blocks and ops are read straight into the IR,
with the text positions that decoding reports kept beside them in the order of
a depth-first walk. When the grammar fails, the rest of the text is still read,
and an error in its characters or tokens wins
([rust-ir-and-tools-funk.md](rust-ir-and-tools-funk.md#report-format)).

`funk` runs on its main thread, with no large reserved stack. A panic exits with
status 2. On 256 KiB threads, `tests/deep.rs` parses, verifies, clones,
compares, hashes, debug-formats and drops a million levels of attributes and of
regions, prints the attributes, and parses and drops a million levels of items.
Regions are printed 3,000 levels deep, which already overflows a printer that
recurses. `funk verify` and `funk fmt` give their verdicts on files a million
levels deep with a 1 MiB stack.

Since `Attr` and `Region` implement `Drop`, code cannot move a field out of an
owned one. It borrows, clones or uses `std::mem::take`. Code in `funk-ir` walks
with `walk` or `Region::parts`. Other crates walk the public fields with an
explicit stack of their own. A walk that recurses once per level is a bug
anywhere. The same holds for calls: the pass that summarizes each function's
effects walks the call graph with its path on the heap, so a long chain of calls
takes no stack per call (ADR-2026-11-10-2108). Memory bounds depth, not the stack. The canonical text of nested
regions grows with the square of their depth, so `funk fmt` streams it
([rust-ir-and-tools-funk.md](rust-ir-and-tools-funk.md#funk-fmt)).

### Constants near a width's limit

A core `const` must fit its type, and a width goes up to 16,777,215 bits
(ADR-2026-11-03-1000). `funk-ir` holds a constant as its decimal spelling.
`Int::fits_signed` decides most digit counts from bounds on log2(10). When the
count does not decide, it computes `2^(w-1)` in decimal and compares it with the
magnitude, digit count first, then digit by digit: below fits, equal fits only
when negative, above does not. The digits are never converted to binary, which
was quadratic: minutes per constant (#37). `Nat::from_decimal` stays quadratic,
so nothing on the path that checks a constant may use it.

`2^k` is built by squaring and doubling, in base-10^5 limbs, in
`crates/funk-ir/src/ir/int/decimal.rs`. Each thread keeps the last power it
built in `LAST_POW2`, about 8 MB at `i16777215`. Squaring uses an NTT over `2^64 - 2^32 + 1`, in
`ir/int/ntt.rs`, with no `unsafe`. Every `u32` width is exact, and an `assert!`
guards the bound. Correctness rests on tests against the quadratic code and on
the coefficient bound. A change of base must recheck that bound. Rejected:
Karatsuba, about 50 times the work at half a million limbs, too slow for a
debug-build test; and a big-integer crate, the first dependency for under 200
lines of code.

## Unsafe code

`unsafe_code = "forbid"` applies to the whole workspace, and the workspace has
no unsafe code (ADR-2026-11-09-1603). Each library root also holds
`#![doc(test(attr(forbid(unsafe_code))))]`, because cargo does not pass
`[lints]` to doctests (ADR-2026-11-03-0808).

The rule stays: any unsafe Rust needs a Verus proof with a listed trusted base
(ADR-2026-11-03-0808). The human ruled it on 2026-11-03 (#117): "If we have
unsafe rust code at all we need to use verus to prove it's fine". The same day
the human ruled the honest-mistake guard: the checks catch careless or
well-meaning changes, and review of the diff is the defence against a
deliberately disguised one. Lowering `forbid` needs a new ADR and a human
ruling. A new verified module, or a change to a trusted base or to the
specification it is proved against, needs a human ruling, and its PR edits
ADR-2026-11-03-0808 in place with every new digest, so the reviewer sees each
one change. Rejected: `deny` in place of `forbid`, since any module could then
allow unsafe code in one line and only review would catch it.

The tooling that enforced the rule is gone from the tree: the human ruled on
2026-11-09 (#168, option 2) to drop the crate `funk-start-fds`, keep the rule
and tag the tooling (ADR-2026-11-09-1603). Its hooks, its scripts, the Verus
download in CI and the `vstd` dependency went with it. The verified module,
trusted base, digests and check rules of ADR-2026-11-03-0808 wait at the tag
`verus-tooling-m0`, on commit `0f070ff`, in that commit's copy of the ADR. So
does the Verus pin: Verus 0.2026.11.02.8bf68ee on Rust 1.99.1, with vstd
`=0.0.0-2026-11-01-0251` from crates.io and `scripts/check-verus.sh`. A bump
there was one PR that moved the release and its SHA-256 in the workflow, the
script's pin, vstd's version and, when needed, the Rust pin; Dependabot ignored
vstd and the `verus_*` crates. Rejected for that pin: the `verus` binary with no
vstd dependency, which needs the proof behind `cfg(verus_keep_ghost)` and can
hide code from it; and Verus's rolling release, which changes every day.

The first real unsafe code, likely the M6 JIT, restores the tooling from that
tag instead of rebuilding it. Restoring it is work: its checkers name
`funk-start-fds`, and its Verus pin must run on the Rust toolchain of that day.
Rejected: keeping the crate and its proof (#168, option 1), since every PR paid
for 246 lines that serve a case the harness never runs.

## Other tools

[testing-and-harness.md](testing-and-harness.md#the-fir-explorer) describes
the fir explorer. Its native runs keep the harness's data limit.
