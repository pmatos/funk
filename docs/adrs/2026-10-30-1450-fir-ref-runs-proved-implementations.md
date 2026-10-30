# `fir-ref` runs implementations of the spec's functions that are proved equal to them and registered with `@[csimp]`

Status: accepted

## Context

fir has no nesting limit: `fir-ref`, like every tool, must give a verdict
on a text nested to any depth, without a stack overflow (the ruling on
[#36](https://github.com/pmatos/funk/issues/36), ADR-2026-10-30-1250).
[#47](https://github.com/pmatos/funk/issues/47) also asks that it print in
time linear in the text it writes.

The spec's readers, decoder and printer are readable recursive definitions
in `lean/Fir/`. They recurse once per level of nesting, most of them once
per list element too, without a tail call. The printer also copies the text
of each list's tail and of each nested region, so its time is quadratic in
the length of a block and cubic in the depth of regions. The measurements
are in #47.
[#11](https://github.com/pmatos/funk/issues/11) proves facts about these
definitions, so they keep their shape.

Facts about Lean:

- `@[csimp]` on a theorem `@f = @g` makes the compiler compile every use of
  the constant `f` as `g`. It acts on code compiled after the theorem is in
  scope; code compiled earlier keeps calling `f`. Proofs, and the kernel,
  still see `f`.
- The compiler turns a function's call to itself in tail position into a
  jump, so such a loop takes no stack, however its termination is proved.

## Decision

- **For each spec function on `fir-ref`'s path that takes stack per level
  or more than linear time, `fir-ref` runs an implementation proved equal
  to it.** The implementation is a loop whose recursive calls are all tail
  calls. It keeps what is left to do on an explicit stack of frames, and
  writes its output into one accumulator. It is defined by well-founded
  recursion on a measure of its frames: total, with no fuel.
- **Each is registered with a theorem `@[csimp] theorem : @specFn = @fastFn`.**
  The proof states one invariant of the loop, such as
  `loop acc frames = acc ++ String.join (frames.map Frame.text)`, where a
  frame's text is the spec function applied to it, and proves it by
  functional induction on the loop, one equation lemma of the spec function
  per case. No `sorry`, `partial`, `unsafe`, `implemented_by` or
  `native_decide`; the proofs use only `propext`, `Classical.choice` and
  `Quot.sound`, which `FirTest` checks with `#print axioms`.
- **They live in `lean/FirRef/`**, which the document does not render. The
  spec in `lean/Fir/` does not change for them, so #11's theorems about the
  spec's functions hold for what `fir-ref` runs.
- **`FirRef.Fast` imports every module that registers such a theorem, and
  `FirRef.Utf8` imports `FirRef.Fast`.** `FirRef.Main` and `FirTest` import
  `FirRef.Utf8`, so all their code is compiled after the theorems. An
  implementation that calls another spec function either comes after that
  function's theorem, or calls a copy of it compiled there: the spec
  compiles `printDefs` before `print_eq_printAttr` exists, so
  `FirRef.PrintModule` prints definitions with its own copy, `defsText`,
  proved equal by `rfl`.
- **The first are the printer's:** `FirRef.printAttr` for `Attr.print`, and
  `FirRef.printModule` for `Module.print`. The decoder, then the readers,
  follow in later stages of #47.

## Alternatives

- **Rewrite the spec's functions as loops.** The spec would lose its
  readable definitions, and #11 would prove facts about machines.
- **`implemented_by`.** It proves nothing: the compiled code could differ
  from the spec without any check failing.
- **Put the implementations in `lean/Fir/`, so that the spec's own later
  code runs them.** `Fir` is the spec (ADR-2026-10-30-1250). The callers
  that matter are replaced as a whole instead: the decoder's implementation
  replaces every caller of `decodeType`, whose error message prints a type.
- **A thread with a larger stack, or one sized from the input.** It moves
  the limit instead of removing it (ADR-2026-10-30-1250), and leaves the
  printer slow.

## Consequences

- The spec stays readable, and what `fir-ref` computes is proved to be what
  the spec defines, byte for byte.
- A spec function compiled before a theorem keeps the slow code, even where
  the compiler specializes it at a later call site: `decodeType`,
  specialized to the core dialect inside `FirRef.Main`, still calls the
  spec's `Attr.print`. Until the decoder's implementation lands, it prints a
  type that does not decode with the spec's `Attr.print`.
- A module of `FirRef` that calls the spec's parser or printer must import
  `FirRef.Fast`, directly or through `FirRef.Utf8`, or it runs the spec's
  code.
- The `#guard` checks and `#eval`s of `FirTest` run the implementations; the
  checks inside `lean/Fir/` run the spec's definitions.
- A change to a spec function breaks its theorem's proof, and so the build,
  until the implementation follows it.
- Each implementation adds proof code; the issue estimates 2,000 to 3,500
  lines for all of them.
