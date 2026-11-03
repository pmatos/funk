# Unsafe Rust needs a Verus proof whose trusted base is listed

Status: accepted

## Context

ADR-2026-11-02-2253 lets one module of `funk-start-fds` hold the
workspace's only unsafe code: a start-up constructor in `.init_array` that
calls `fcntl(fd, F_GETFD)` on descriptors 0 to 2 and records which were
closed. Review alone kept it sound.

The human ruled on 2026-11-03
([#117](https://github.com/pmatos/funk/issues/117)): "If we have unsafe
rust code at all we need to use verus to prove it's fine".
[Verus](https://github.com/verus-lang/verus) proves Rust code against
specifications. It cannot check a foreign function, a link section, or the
value that a standard-library atomic holds: vstd, its standard library,
specifies `AtomicI32` without its value. A piece that Verus cannot check is
trusted: Verus assumes its specification without proof. The human did not
say how to apply the ruling to such pieces. #117 records the reading taken
here: they become explicit, listed specifications, and Verus proves the
rest.

## Decision

- **Unsafe code lives only in a verified module**, in a crate that opts
  in with `[package.metadata.verus] verify = true`, which the `verus-proof`
  hook verifies (ADR-2026-11-03-0809). Its code is inside `verus!`, except
  the trusted pieces that Verus cannot take.
- **One verified module**, `crates/funk-start-fds/src/record.rs`. Verus
  proves `record`, the constructor, against #117's specification: when it
  returns, slot `fd` of `CLOSED` holds the OS error that
  `fcntl(fd, F_GETFD)` failed with, for `fd` in 0 to 2, and 0 when it did
  not fail with one. `record` takes the view of the slots once, has
  `record_slots` fill them, and ends by passing the view to `finish`, a
  proof function that requires the specification and consumes the view.
  `Slots` cannot be copied and only `record` takes a view, so no store
  follows `finish`. Every index is in bounds and nothing panics
  (`no_unwind`).
- **The trusted base**, in `crates/funk-start-fds/src/record.rs`, each item
  marked TRUSTED in the code with its specification:
  - the `fcntl` extern block: POSIX's variadic `fcntl`, from the C library.
  - `getfd`: calls `fcntl(fd, F_GETFD)`, then reads `errno` with
    `io::Error::last_os_error().raw_os_error()`. Assumes it returns without
    panicking and writes no memory the program owns. Its result may be any
    `c_int`, named `getfd_result(fd)`; when it is -1, `errno` holds that
    call's error, named `getfd_error(fd)`, since nothing runs between the
    two. Both names depend on `fd` alone, so every call on one descriptor
    gives the same answer. That holds while `record` runs: nothing else
    runs then, and `F_GETFD` changes nothing. It requires
    `0 <= fd < 3`, so it assumes nothing of any other descriptor.
  - `Slots`: a ghost token that stands for the three slots of `CLOSED`;
    `holds(fd)` is what slot `fd` holds. Its field is
    `::core::cell::Cell<()>`. A `Cell` is not `Copy`, so rustc rejects any
    `Copy` for `Slots`. The built crate never constructs it:
    `Tracked<&mut Slots>` is a zero-sized `PhantomData`, and `take_slots`
    is erased.
  - `store`: stores `code` in `CLOSED[fd]`, through a reference typed
    `&[AtomicI32; 3]`, so rustc checks that `CLOSED` has the three slots
    that `fd < 3` assumes. Assumes that afterwards slot `fd` holds `code`
    and no other slot changed.
  - `take_slots`, an `axiom fn`, and `RECORD`, the
    `#[unsafe(link_section = ".init_array")]` static: the `.init_array`
    contract. The C runtime calls `record` once, on the main thread, before
    `main` and before any other thread exists, with the C calling
    convention. No file of the crate but `record.rs` uses vstd or
    `verus!`, so verified code cannot name `CLOSED`, and in the verified
    module only `store` writes it, called only by `record_slots`. So
    `record` alone uses `CLOSED` while it runs, and `take_slots` hands it
    the one `Slots`. Nothing is assumed of what the slots hold.
  - the module's `#![allow(unsafe_code)]`, under the crate's
    `unsafe_code = "deny"`.
- **The text of the trusted base, of #117's specification and of `record`
  is pinned**: `scripts/unsafe_pins.py` keeps a digest of each one's
  tokens, without comments or layout but with attributes and string
  literals, and the check fails when the text no longer has it. An item's
  text is that of every item of its name, inside `verus!` or not, so a
  second item of a trusted item's name changes it. Only `record_slots`'
  body, which Verus proves against its pinned signature, and new items
  inside `verus!`, which Verus checks, change without a new pin. The
  digests, which running that file prints:
  - everything outside `verus!`, which holds the inner attribute, the
    `use` items, `F_GETFD`, the `fcntl` block and `RECORD`:
    `62c33443a91b98483be1c03787b79b88`;
  - the inner attribute: `14463c81dd47caad0f05c576569075a7`;
  - the `fcntl` block: `5f7e97dcda1b9d3316c485f8a7d68231`;
  - `RECORD`: `164d4da18a4fa67336936955f1dce68d`;
  - `getfd_result`: `8a11764c47df02dc60910cd9c29390f7`;
  - `getfd_error`: `205e7fafe7fdab6640934d7d2a004358`;
  - `recorded`: `326ffb47b78d0047a16fca535e91d8f6`;
  - `getfd`: `01a5f7c3c0242be238824df243d82c5e`;
  - `Slots`, with its `impl` and `holds`:
    `e2fb744c0eea21724cbe816093227e12`;
  - `take_slots`: `0f4d1d6cf21e96e05482d5f77048a462`;
  - `store`: `a053251f8a0ba7a82a906ae6389e9c20`;
  - `record_slots` up to its body, so its signature and `ensures`:
    `ec6ad38b80605048affda900cf3d72b4`;
  - `finish`: `6be258f6fe1429e777f506d7ce6a4ade`;
  - `record`: `889180278b8ce3b1478ad6bb4ad2efdf`.
- **`record` stores every slot**, 0 for an open descriptor, where it
  stored nothing before. The slot held 0 already, so funk behaves as
  before, and the proof needs no assumption on the slots' first values.
- **What the check guards against.** The `unsafe-code` check catches
  careless or well-meaning changes, such as an `unsafe` block written into
  `record_slots`' body, an `assume` left from a proof in progress, or a
  trusted item's `ensures` strengthened to get a proof through. Review of
  the diff is the defence against a deliberately disguised change. The
  human ruled so on 2026-11-03, by dialog (the honest-mistake guard): keep
  the Verus proof, the listed and digested trusted base, and the rules
  that catch careless or well-meaning changes; drop the fences that only
  stop a deliberately disguised change, deciding rule by rule from an
  audit of what each costs legitimate work. Four rules that only stop a
  deliberate change stay, since they cost none: the `check-cfg`,
  `verus`-shadowing, renamed import and `extern crate` rules below.
- **The rules that remain.** `scripts/check_unsafe_code.py` reads every
  tracked Rust file and manifest, Rust by tokens, without comments, a
  string literal as one token, and a raw identifier such as
  `r#external_body` as the plain one. Its tests plant each kind of
  violation. Each rule, and what it asks of future work:
  - in every crate:
    - `unsafe`, as a block, function, trait, impl, extern block or
      `unsafe(...)` attribute, only on a trusted item, inside `verus!` too:
      Verus accepts some unsafe code there without a check, such as an
      `unsafe impl` (verus-lang/verus#3184). More unsafe code needs a new
      verified module, a new ADR and a human ruling;
    - `unsafe_code` in an attribute only as a lint of `forbid(...)` or
      `deny(...)`, besides the trusted one; the lints before it may be
      paths, as in `deny(clippy::all, unsafe_code)`. No `allow`, `warn` or
      `expect` of it;
    - `[workspace.lints]` keeps `unsafe_code = "forbid"`, and a crate with
      no verified module has `[lints] workspace = true` or sets
      `unsafe_code = "forbid"` in its own `[lints.rust]`, which then
      repeats each workspace lint it keeps;
    - each library root holds `#![doc(test(attr(forbid(unsafe_code))))]`,
      as an inner attribute of its own, even with `doctest = false`: cargo
      passes `[lints]` to every target but doctests;
    - no identifier that starts with `verus_`: Verus sets configurations
      of such names and cargo does not, so they select code that Verus may
      not see. Such a word is renamed, even in a crate without vstd;
    - no manifest declares a `verus_*` cfg to `check-cfg`;
    - no `as verus` and no `macro_rules! verus`, which would shadow vstd's
      `verus!`;
  - in a crate that uses vstd:
    - no `assume`, `admit`, `axiom`, `external`, or word that starts with
      `assume_` or `external_`, such as `external_body`,
      `assume_specification` or `Tracked::assume_new`, but on a trusted
      item. Such a name is renamed, even a local one and in tests;
    - no `verifier::` or `verus::` attribute but `verifier::external_body`
      on a trusted item: `exec_allows_no_decreases_clause` lets `loop {}`
      prove anything. A new proof carries no `rlimit`, `opaque`,
      `spinoff_prover` or `loop_isolation`;
  - in a crate with a verified module:
    - `unsafe_code = "deny"` in its own `[lints.rust]`. Keeping the
      workspace's other lints in step is a convention that its
      `Cargo.toml` comment states, not a check;
    - `[package.metadata.verus] verify = true`;
    - no file but a verified module uses vstd or calls `verus!`, so
      verified code can name none of the crate's other items, such as
      `CLOSED`. Specifying more of the crate needs a new verified module;
    - no `extern crate`, which could rename a crate that a pinned text
      names;
  - in a verified module:
    - outside `verus!`, only inner attributes, `use`, constants and
      trusted items, since Verus would not see a function there. New code
      goes inside `verus!`; that text is pinned, so a lemma's import is a
      full path;
    - no macro call but the one `verus!` block, and no `macro_rules!`:
      Verus and cargo may expand a macro differently, as `cfg!` and
      `option_env!` do. A new lemma uses no `calc!` or `seq!`;
    - no `cfg` or `cfg_attr`: Verus checks only what its host selects. The
      module holds no `#[cfg(test)]` tests and no per-target code;
    - no `use ... as`, which could make a macro pass for a keyword;
    - `take_slots` and `finish` named once, in `record`; `getfd` and
      `store` once, in `record_slots`; `record` once, in `RECORD`; a method
      call after `.` does not count. So `record_slots` names `getfd` and
      `store` once each and none of the other three, and a helper of it
      names none of the five, not even as a local name;
    - the pinned texts above. A change needs a new ADR, a human ruling and
      the new digest;
    - a trusted item carries only its listed marks, each still in use, so
      a stale entry cannot trust a new item of the old name;
  - in the hooks:
    - `verus-proof` runs the pinned Verus release on the pinned Rust, and
      fails unless Verus saw and proved each function that
      `scripts/verus_report.py` names for the crate, `record` and
      `record_slots` for `funk-start-fds`, so a `cfg` that hides the
      module from Verus fails it. A crate that opts in lists its functions
      there. A commit that touches `crates/`, a Cargo file or the Rust pin
      needs that release installed (ADR-2026-11-03-0809);
    - `unsafe-code-test` checks that this ADR names every trusted item and
      every digest.
- **A change to the trusted base or to #117's specification**, which
  changes a pinned text, or a new verified module needs a new ADR and a
  human ruling, as ADR-2026-11-02-2253 asks of a new exception. That ADR
  restates every digest, since this one is immutable, and `ADR` in
  `scripts/check_unsafe_code.py` points at it: the test that the ADR lists
  every digest reads that file alone.

This refines ADR-2026-11-02-2253: its module stays the only unsafe code,
and now carries a proof.

## Alternatives

- **`deny` instead of `forbid` in the workspace.** Any module could then
  allow unsafe code in one line, and only review would catch it.
- **vstd's `PAtomicI32`**, whose permission tokens give its value. Its
  permissions would have to live in a ghost invariant of the static, which
  changes `CLOSED` and `closed_at_start`. `Slots` trusts one fact, the one
  `store` states.
- **Verus's `#[verus_spec]` attributes** instead of `verus!`: its loop
  invariants need the unstable `proc_macro_hygiene` feature.
- **A `for` loop**, as before: vstd lets an iterator panic, so Verus cannot
  show `no_unwind`. `record_slots` uses a `while` loop.

## Consequences

- Verus proves the constructor's logic, bounds and freedom from panics.
  Review covers the trusted items, a few lines each, and any change that
  disguises unsafe code from the check: it reads tokens, not Rust's
  meaning, and leaves to rustc what its lints enforce.
- The check fails on unsafe code or an assumption outside the list, and
  on any edit to a pinned text, so neither changes without the ADR that a
  change needs. It over-approximates: a name such as `external_count` in
  a crate that uses vstd fails, and so does `verus_version` in any crate;
  each is renamed.
- `record_slots` may gain exec, proof or spec helpers inside `verus!`,
  which Verus proves, without a new ADR.
- Verus checks the module on x86-64 Linux, in CI; the other ELF Unix targets
  build the same source.
