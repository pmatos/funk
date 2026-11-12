# Unsafe Rust needs a Verus proof whose trusted base is listed

Status: accepted
Tier: direction; area: rust-ir-and-tools

## Decision

- **Unsafe code lives only in a verified module**, in a crate that opts in
  to [Verus](https://github.com/verus-lang/verus). The module's code is
  inside `verus!`, and Verus proves it against its specification, its bounds
  and its freedom from panics.
- **The trusted base is listed.** A piece that Verus cannot check, such as a
  foreign function, a link section or the value of a standard-library
  atomic, is trusted: Verus assumes its specification. Each trusted item is
  marked TRUSTED in the code with its specification, and this ADR lists it.
- **The texts are pinned.** A check keeps a digest of the tokens of each
  trusted item, of the specification and of the function proved against it,
  and fails when a text no longer has its digest. This ADR lists every
  digest, and the check reads them from this file.
- **What the check guards against.** It catches careless or well-meaning
  changes: an `unsafe` block, an `assume` left from a proof in progress, a
  trusted item's specification strengthened to get a proof through. Review
  of the diff is the defence against a deliberately disguised change.
- **Changing it.** A new verified module, or a change to a trusted base or
  to the specification it is proved against, needs a human ruling. Its PR
  edits this ADR in place with the trusted items and every new digest, so
  the reviewer sees each one change. Lowering `forbid` needs a new ADR and a
  human ruling (AGENTS.md).
- **Outside a verified module**, `unsafe_code = "forbid"` holds, and each
  library root holds `#![doc(test(attr(forbid(unsafe_code))))]`, because
  cargo does not pass `[lints]` to doctests.

Today no crate has a verified module (ADR-2026-11-09-1603). The last one,
in `crates/funk-start-fds`, its trusted base, its digests, the check's rules
and the Verus pin are in this file at the tag `verus-tooling-m0` (commit
`0f070ff`). The first real unsafe code restores them from there.

## Why

The human ruled on 2026-11-03
([#117](https://github.com/pmatos/funk/issues/117)): "If we have unsafe
rust code at all we need to use verus to prove it's fine". Verus cannot
check every piece, so those pieces become explicit, listed specifications,
and Verus proves the rest. The same day the human ruled the honest-mistake
guard, by dialog: keep the proof, the listed and digested trusted base and
the rules that catch careless changes, and drop fences that only stop a
deliberately disguised change.

## Rejected alternatives

- **`deny` in place of `forbid` in the workspace.** Any module could then
  allow unsafe code in one line, and only review would catch it.
- **vstd's `PAtomicI32`**, whose permission tokens give its value. Its
  permissions would need a ghost invariant of the static; a ghost token that
  trusts one fact is smaller.
- **Verus's `#[verus_spec]` attributes** in place of `verus!`: its loop
  invariants need the unstable `proc_macro_hygiene` feature.
