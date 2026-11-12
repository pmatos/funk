# The Lean build fails on sorry, untrusted axioms, unsafe code and any warning, and trusts native evaluation

Status: accepted
Tier: direction; area: spec-site

## Decision

- The root of `FirTest` imports every module of `lean/` and runs
  `#check_axioms Fir FirRef FirTest` as its last command. It fails, naming
  each declaration, on one that:
  - depends on an axiom other than `propext`, `Classical.choice`,
    `Quot.sound` or an axiom of native evaluation;
  - is `unsafe`, or is an opaque constant with an `_unsafe_rec`, which is
    what `partial` makes;
  - has an `implemented_by` or an `extern` attribute.
- An axiom counts as native evaluation only when its claim is `e = true`
  for a closed `e : Bool` and the check runs `e` again and gets `true`
  ([the page](../decisions/spec-site-lean-build.md#what-lean-code-in-lean-may-not-do)
  has the exact test). So `native_decide`, `decide +native` and native
  `bv_decide` are allowed. The human ruled to trust Lean's compiler on
  2026-10-30, in #52.
- A `@[csimp]` swap rests on `propext`, `Classical.choice` and `Quot.sound`
  alone. The human accepted this narrowing on 2026-11-02, in #52.
- `scripts/build-spec.sh` builds `lean/` with `lake build --wfail`, so any
  warning fails the build, a `sorry` inside an `example` included. The human
  ruled this on 2026-10-30, in #52. The build in `docs/spec/` stays a plain
  `lake build`, because Verso's build can warn about code we do not own.
- Code that must be `partial`, `unsafe` or `extern` stays out of `lean/`
  until this ADR is edited to allow it.

## Why

`fir-ref` runs the definitions that the proofs are about, so the code that
Lean compiles must not differ from them, and no proof may rest on a claim
nobody checked. An `example` is not a declaration, so the check never sees
one; only `--wfail` catches a `sorry` in it. Native evaluation adds Lean's
compiler and runtime to the trusted base, and the bans on `unsafe`,
`partial`, `implemented_by` and `extern` keep compiled code equal to the
proved definitions. A swap proved from a native axiom could make that
axiom's false claim run as `true` when the check runs it again.

## Rejected alternatives

- **A text search for `sorry`, `partial` and the rest.** It cannot see
  axioms used through other declarations, nor code that a macro writes, and
  prose may use the words.
- **`#print axioms` for each theorem.** A missing line passes in silence.
- **A separate executable or hook that loads the built modules.** It is a
  second Lake entry point to guard.
- **A text check that bans `native_decide`.** Proposed, then dropped when the
  human chose to trust the compiler.
- **Keeping warnings as warnings.** A `sorry` inside an `example` would pass.
