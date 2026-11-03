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
  proves `record_slots` against #117's specification: afterwards, slot `fd`
  of `CLOSED` holds the OS error that `fcntl(fd, F_GETFD)` failed with, for
  `fd` in 0 to 2, and 0 when it did not fail with one. Every index is in
  bounds and nothing panics (`no_unwind`). `record`, the constructor, calls
  it.
- **The trusted base**, in `crates/funk-start-fds/src/record.rs`, each item
  marked TRUSTED in the code with its specification:
  - the `fcntl` extern block: POSIX's variadic `fcntl`, from the C library.
  - `getfd`: calls `fcntl(fd, F_GETFD)`. Assumes it returns without
    panicking and writes no memory the program owns. Its result may be any
    `c_int`, named `getfd_result(fd)`.
  - `last_error`: `io::Error::last_os_error().raw_os_error()`. Assumes that,
    called right after `getfd(fd)` returned -1, it gives the error of that
    call, named `getfd_error(fd)`.
  - `Slots`: a ghost token that stands for the three slots of `CLOSED`;
    `holds(fd)` is what slot `fd` holds. The build erases it.
  - `store`: `CLOSED[fd].store(code, Relaxed)`. Assumes that afterwards
    slot `fd` holds `code` and no other slot changed.
  - `take_slots`, an `axiom fn`, and `RECORD`, the
    `#[unsafe(link_section = ".init_array")]` static: the `.init_array`
    contract. The C runtime calls `record` once, on the main thread, before
    `main` and before any other thread exists, with the C calling
    convention. So `record` alone uses `CLOSED` while it runs, and
    `take_slots` hands it `Slots`. Nothing is assumed of what they hold.
  - the module's `#![allow(unsafe_code)]`, under the crate's
    `unsafe_code = "deny"`.
- **`record` stores every slot**, 0 for an open descriptor, where it
  stored nothing before. The slot held 0 already, so funk behaves as
  before, and the proof needs no assumption on the slots' first values.
- **The `unsafe-code` check**, `scripts/check_unsafe_code.py`, reads every
  tracked Rust file and manifest, without comments and strings. Its tests
  plant each kind of violation, and check that this ADR names every trusted
  item. It fails on:
  - `unsafe` (a block, function, trait, impl or extern block, or an
    `unsafe(...)` attribute) other than inside `verus!` in a verified
    module or on a trusted item;
  - `unsafe_code` in an attribute, such as `allow(unsafe_code)`, other than
    the trusted one, and `unsafe_code` below `forbid` in the manifest of a
    crate with no verified module;
  - in a crate that uses vstd, `assume`, `admit`, `axiom`, `external` or a
    word that starts with `assume_` or `external_`, such as
    `external_body` and `assume_specification`, other than on a trusted
    item;
  - `verus_keep_ghost` and `verus_only`, and `cfg` or `cfg_attr` in a
    verified module: they select code that Verus may not see;
  - a verified module whose crate does not opt in, and a trusted item that
    is gone.
- **A change to the trusted base** or a new verified module needs a new
  ADR and a human ruling, as ADR-2026-11-02-2253 asks of a new exception.

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
- The check fails on unsafe code or an assumption outside the list, so a
  new one cannot slip in through review.
- Verus checks the module on x86-64 Linux, in CI; the other ELF Unix targets
  build the same source.
