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
    `Copy` for `Slots`, and the leading `::` names the real `core`, which
    no local item can shadow. The built crate never constructs it:
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
    convention. `lib.rs`, pinned whole, uses neither vstd nor `verus!`, so
    Verus cannot name `CLOSED`, and in the verified module only `store`
    writes it, called only by `record_slots`. So `record` alone uses
    `CLOSED` while it runs, and `take_slots` hands it the one `Slots`.
    Nothing is assumed of what the slots hold.
  - the module's `#![allow(unsafe_code)]`, under the crate's
    `unsafe_code = "deny"`.
- **The text of the trusted base, of #117's specification, of `record`
  and of `lib.rs` is pinned**: `scripts/unsafe_pins.py` keeps a digest of
  each one's tokens, without comments or layout but with attributes and
  string literals, and the check fails when the text no longer has it. An
  item's text is that of every item of its name, inside `verus!` or not,
  so a second item of a trusted item's name changes it. `lib.rs` is pinned
  whole: it defines `CLOSED`, which `store` writes, and `Stream` and
  `closed_at_start`, which read it; it mounts the verified module, so its
  `cfg` decides where the proof applies; and an `extern crate` there could
  rename `std` for the module. Only `record_slots`' body, which Verus
  proves against its pinned signature, and new proof or spec functions
  inside `verus!` whose names no pinned text holds, change without a new
  pin. The digests, which running that file prints:
  - `crates/funk-start-fds/src/lib.rs`, whole:
    `eff716f8cabc359b6255f82d9c23f9a8`;
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
- **The `unsafe-code` check**, `scripts/check_unsafe_code.py`, reads every
  tracked Rust file, manifest and Cargo configuration. It reads Rust by
  tokens, without comments, a string literal as one token, and a raw
  identifier such as `r#external_body` as the plain one. Its tests plant
  each kind of violation, and check that this ADR names every trusted item
  and every digest. It fails on:
  - `unsafe` (a block, function, trait, impl or extern block, or an
    `unsafe(...)` attribute) other than on a trusted item, inside `verus!`
    too: Verus accepts some unsafe code there without a check, such as an
    `unsafe impl` (verus-lang/verus#3184);
  - a pinned text that changed;
  - in a verified module: an item outside `verus!` other than inner
    attributes, `use`, a constant and a trusted item; an item inside
    `verus!` that is neither pinned nor a proof or spec function, and a
    new one whose name a pinned text holds, since a pin holds tokens, not
    what names resolve to: `type int = u8;` or a `mod core` would change
    what a pinned text means; a call of any macro, such as `option_env!`
    or `global_asm!`, or a `macro_rules!`, other than the one `verus!`
    block, since Verus and cargo may expand one differently and the check
    does not see what one makes; and a `use` that renames, which could
    make a macro look like a keyword;
  - in a crate with a verified module: vstd or `verus!` in any other
    file, so Verus can name none of its items, and any `extern crate`;
  - a name that the proof rests on in the wrong place: `take_slots` and
    `finish` named other than once, in `record`; `getfd` and `store` other
    than once, in `record_slots`; `record` other than once, in `RECORD`;
    and `Slots` in any item but those that pass the view along. A method
    call after `.` does not count;
  - `macro_rules! verus` or `as verus` anywhere, which would shadow vstd's
    `verus!`, and in a crate that uses vstd, `include!` or a `path`
    attribute, which take code from a file the check may not read;
  - `unsafe_code` in an attribute other than `forbid(...)` or
    `deny(...)`, such as `allow(unsafe_code)`, besides the trusted one;
    the lints before it may be paths, as in `deny(clippy::all,
    unsafe_code)`;
  - in a crate that uses vstd, `assume`, `admit`, `axiom`, `external` or a
    word that starts with `assume_` or `external_`, such as
    `external_body` and `assume_specification`, other than on a trusted
    item; and any `verifier::` or `verus::` attribute but
    `verifier::external_body`, such as `exec_allows_no_decreases_clause`,
    with which `loop {}` proves anything;
  - a word that starts with `verus_`, such as `verus_keep_ghost`, a
    manifest that declares one to `check-cfg`, and `cfg` or `cfg_attr` in
    a verified module: Verus sets those configurations and cargo does not,
    so they select code that Verus may not see;
  - a verified module whose crate does not opt in, one that its parent
    does not mount by one `mod` item, a `mod` item that carries anything
    but a `target_os` cfg, and a trusted item that is gone;
  - in the manifests, `scripts/unsafe_manifests.py`: `[workspace.lints]`
    without `unsafe_code = "forbid"`, a crate with no verified module that
    neither inherits it nor forbids unsafe code, and a crate with a
    verified module whose `unsafe_code` is not `deny`; a crate or a
    target not on the workspace's 2024 edition, in which an extern block
    and an unsafe attribute must say `unsafe`; a target `path` that is not
    a tracked `.rs` file; a crate with a verified module that sets one, or
    depends on anything but vstd by its version; a `[patch]` or
    `[replace]` of vstd or a `verus_*` crate; a proc-macro crate, since
    rustc does not report `unsafe_code` in a proc macro's output, even at
    `forbid`; and a build script, a `build` key other than `false` or a
    `links` key in any crate, and a tracked `.cargo/config.toml` or
    `.cargo/config`, each of which can link code that no `.rs` file holds;
  - a library whose root lacks `#![doc(test(attr(forbid(unsafe_code))))]`:
    cargo passes `[lints]` to every target but doctests.
- **The `verus-proof` hook** also fails unless Verus saw and proved
  `record` and `record_slots`, which `scripts/verus_report.py` names for
  `funk-start-fds`, so a cfg that hides the module from Verus but not from
  cargo fails it, whatever else Verus verified. A crate that opts in
  without such a list fails too.
- **A change to the trusted base or to #117's specification**, which
  changes a pinned text, or a new verified module needs a new ADR and a
  human ruling, as ADR-2026-11-02-2253 asks of a new exception; the new
  digests go in the check and in that ADR.

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
  Review covers only the trusted items, a few lines each.
- The check fails on unsafe code or an assumption outside the list, and
  on any edit to a pinned text, so neither changes without the ADR that a
  change needs. It reads tokens, not Rust's meaning, and leaves to rustc
  what its lints enforce, except where rustc does not report them: in a
  proc macro's output, so the workspace has no proc-macro crate. It
  over-approximates: a name such as `external_count` in a crate that uses
  vstd fails too, and is renamed. A helper of `record_slots` is a proof or
  spec function, or code in its body; a new exec function needs a new ADR.
- Verus checks the module on x86-64 Linux, in CI; the other ELF Unix targets
  build the same source.
