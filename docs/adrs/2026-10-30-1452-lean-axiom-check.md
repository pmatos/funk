# The Lean build fails on sorry, non-standard axioms, unsafe, partial, implemented_by and extern

Status: accepted

## Context

[#11](https://github.com/pmatos/funk/issues/11) proves that parsing a printed
module gives the module back, and that the core dialect's text is lawful.
Its acceptance criteria ask for a check in `.pre-commit-config.yaml` that
fails the build on a `sorry`, or on any axiom other than Lean's standard
three: `propext`, `Classical.choice` and `Quot.sound`. The check must run
Lake only through `scripts/build-spec.sh` or with its git guards
(ADR-2026-10-29-2135).

Facts, checked on 2026-10-30 with Lean `v4.35.0`:

- A `sorry` makes a declaration depend on the axiom `sorryAx`, and
  `native_decide` on an axiom of its own. `Lean.collectAxioms` lists the
  axioms that a declaration depends on, through every declaration it uses.
- `partial`, `unsafe`, `implemented_by` and `extern` add no axiom, yet each
  one lets compiled code differ from what the proofs are about. A `partial`
  definition is an opaque constant whose code is its `_unsafe_rec`.
  Well-founded recursion also makes an `_unsafe_rec`, for the compiler,
  beside a definition that has a value. An `extern` definition with a body
  is proved about through its body and runs as the C function it names.
- A derived `Repr` instance of a type that holds a list of itself, such as
  `Attr`, is `partial`.
- Lake builds only the modules that a library's root imports. The root of
  `FirTest` can import the roots of `Fir` and `FirRef` and the executable's
  `FirRef.Main`, and so see every module that Lake builds in `lean/`. A
  file in `lean/Fir/` that no module imports is not built, yet the spec
  document can still render it with `includeLiterate`.
- The environment lists the declarations of each imported module, and
  separately those of the module being elaborated, up to the current
  command.
- Lean does not keep an `example`. A `sorry` in one is a warning, and
  `lake build --wfail` fails on any warning. `lean/` builds with none.

## Decision

- `FirTest/Axioms.lean` defines the command `#check_axioms`. The root of
  `FirTest` imports every module of `lean/` and runs
  `#check_axioms Fir FirRef FirTest` as its last command. It fails, naming
  each declaration, when a declaration of those libraries, or of the root
  itself, does one of these:
  - depends on an axiom other than `propext`, `Classical.choice` and
    `Quot.sound`;
  - is `unsafe`, or is an opaque constant with an `_unsafe_rec`, which is
    what `partial` makes;
  - has an `implemented_by` or an `extern` attribute.
- It also fails when:
  - a `.lean` file in `lean/`, other than `lakefile.lean` and the files
    under a hidden directory such as `.lake`, is not imported by the root,
    or its module is not under one of the roots it names;
  - a root has no declaration, so that a renamed library is not skipped in
    silence;
  - any text but white space follows it, since it would not see a command
    there.
- `scripts/build-spec.sh` builds `lean/` with `lake build --wfail`, so a
  warning, such as a `sorry` in an `example`, fails the build.
- The check runs whenever Lake builds `FirTest`: in the `fir-spec` hook,
  through `scripts/build-spec.sh`, and in every script that calls
  `scripts/build-spec.sh --lean`. It needs no new Lake call. The hook's name
  says that it checks axioms.
- `Attr`'s `Repr` instance is written by structural recursion, not derived.
- `FirTest/Axioms.lean` imports Lean's own modules (`Lean.Util.CollectAxioms`,
  the attributes and the elaborator). They are part of the toolchain, not a
  dependency of the package `fir`.

## Alternatives

- **A text search for `sorry`, `partial` and the rest.** It cannot see the
  axioms that a declaration uses through other declarations, nor the code
  that a deriving handler or a macro writes, and prose may use the words.
- **`#print axioms` for each theorem.** Each new theorem would need a line,
  and a missing line would pass in silence.
- **A separate executable or hook that loads the built modules.** It would
  be a second Lake entry point to guard, for what building `FirTest`
  already does.

## Consequences

- No declaration in `lean/` can rest on `sorry`, `native_decide` or another
  axiom, and `fir-ref` runs the definitions that the proofs are about.
  [#47](https://github.com/pmatos/funk/issues/47) proves its fast
  implementations equal with `@[csimp]`, which the check allows.
- `native_decide` in an `example` is not caught: Lean drops the example and
  its axiom, and gives no warning. No declaration can use an example, so no
  theorem rests on it; a reviewer still rejects one.
- Any warning in `lean/` fails the build, so a toolchain bump fixes its
  deprecation warnings in the same change.
- A new module or library of `lean/` is imported by the root of `FirTest`,
  and a new library is named in its `#check_axioms`; a stray `.lean` file in
  `lean/`, tracked or not, fails the build.
- A type that holds a list of itself writes its `Repr` instance by hand.
- Code that must be `partial`, `unsafe` or `extern` cannot live in `lean/`
  without a new ADR.
