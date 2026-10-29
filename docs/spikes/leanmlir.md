# Spike: should fir's Lean semantics build on LeanMLIR?

Issue [#24](https://github.com/pmatos/funk/issues/24), run on 2026-10-29.
The decision it supports is in
[ADR-2026-10-29-2030](../adrs/2026-10-29-2030-fir-lean-semantics-own-calculus.md).

## The question

Should fir's Lean semantics (#8, #10, #11, #14) build on LeanMLIR's
intrinsically typed SSA framework, or define its own small calculus?

## What was built

Both prototypes are on branch
[`vibe/24-leanmlir-spike-prototypes`](https://github.com/pmatos/funk/tree/e17e4dd4eb7184b7eed2f89301787df7cc763a21/spike)
at commit `e17e4dd`. That code does not merge.

| Package | What it is | Lean |
| --- | --- | --- |
| `spike/own` | fir's own calculus. No dependencies. | v4.35.0, and builds unchanged on the nightly below |
| `spike/leanmlir` | The same piece as a LeanMLIR dialect, plus a CFG layer | `nightly-2025-12-01` |
| `spike/doc` | One Verso page with definitions from both | `nightly-2025-12-01` |

LeanMLIR is [opencompl/lean-mlir](https://github.com/opencompl/lean-mlir) at
`b8c4a771319a044854a4bbb49b8821381ef86ff8` (2026-07-28, the head of `main`).
It pins `leanprover/lean4:nightly-2025-12-01` (Lean 4.27.0-nightly, compiler
commit `5bd331e8`) and Mathlib from `mathlib4-nightly-testing` at
`nightly-testing-2025-12-01`. Verso is at its tag `nightly-2025-12-01`.

Both prototypes model the same piece: parameters, `const`, `add` (with `nsw`,
so that poison can arise), `xor`, `freeze`, `br` and `cond_br` with block
arguments, and `ret`, at any width. Both use one effect monad, `Prog`: the
free monad over "choose `w` bits" and "immediate UB". Its handlers are the two
`fir-ref` modes. The LeanMLIR dialect reuses `Prog` as its dialect monad, so
the comparison isolates the term language.

Both prototypes give the same results, checked by `#guard` at build time:

| Sample | Outcome set (exhaustive mode) |
| --- | --- |
| `add3(40)`: `const`, `add`, `ret` at `i8` | `{43}` |
| `twoBlocks(5, 7)`: `br next(%s, %a)` | `{17}` |
| `add nsw 127, 1` at `i8`, returned | `{poison}` |
| `cond_br` on poison | `{ub "branch on poison"}` |
| `br` to itself | `{fuel exhausted}` |
| `freeze` of poison at `i2`, returned | `{0, 1, 2, 3}` |
| `xor %f, %f` after `freeze` at `i8` | `{0}` (256 choices) |
| same, budget 4 bits | budget exceeded, reported |
| scripted mode, `i2`, script `[3]` | `3`, choice used |

## Fit with the decided semantics

| Point | Own calculus | LeanMLIR |
| --- | --- | --- |
| Poison distinct from UB (S1) | Poison is a value (`PoisonOr`); UB is an effect. | The framework allows it: values can be `PoisonOr`, and UB can be an effect of the dialect monad. The prototype does this. The shipped LLVM dialect folds them: `udiv` by zero returns `.poison` (`Dialects/LLVM/Semantics.lean`, `udiv?`). |
| `freeze` with a choice effect | `freeze` calls `choose`. | Works: `freeze` is an `impure` op in `Prog`. The shipped LLVM dialect makes `freeze poison` return `0` (`Semantics.lean`, `freeze`), the "one fixed value" option that #7 rejects. |
| Refinement over sets of behaviours (S4) | To be defined; `Prog.sem` gives the sets. | Fits: `HRefinement` and `DialectHRefinement` define `⊑` on values and on the dialect monad, "every observable behaviour of b is allowed by a". |
| CFG with block arguments (H1) | Built in: blocks, successors, fuel per block. | Missing. A region is one straight-line `Com` ending in `rets`. The prototype adds a CFG layer outside the framework (below). |
| Isolated from above (H2) | By construction. | Fits: a region's body has its own context. |
| Location on every op (H8) | A field of every op. | Missing. `Expr` has no location. It would go into the op (then rewrite matching and op equality see it) or into a side table keyed by position. |
| Value names stored and printed (P3) | Names are part of the term. | Missing. Variables are de Bruijn indices, and the printer renumbers them (`%{index}`, `Framework/Print.lean`, `printVar`). |
| Parameterized over the dialect (G0) | The same classes as LeanMLIR. | Fits: this is the model G0 names. One difference: a LeanMLIR dialect fixes one monad (`Dialect.m`), while the prototype's ops state the effects they need as class constraints. |

### The CFG layer on LeanMLIR

`spike/leanmlir/FirLeanMLIR/CFG.lean` makes each block a `Com` over its own
arguments. A terminator is an op that returns a value of a new type `ctl`,
which names the next block and carries the arguments. The layer walks blocks
with fuel. It works, but:

- Values cross block boundaries untyped and are checked at run time.
- A block cannot see values of the blocks that dominate it. Everything live
  must be passed as an argument. The epic's `@sum` uses `%n` in `loop`
  without passing it, so fir's semantics would differ from the text.
- LeanMLIR's rewriter, DCE and CSE see one block at a time.

A real CFG in LeanMLIR means changing `Com`, the inductive that every
framework lemma, the zipper, the rewriter and the tactics are built on
(`Framework/Basic.lean` alone is 53 KB). That is a fork, not an extension.
Names and locations need the same kind of change.

## Proof support

**Print then parse (#11).** LeanMLIR's parser cannot be used. It parses
MLIR's syntax, not fir's. It runs Lean's elaborator at run time:
`MLIRSyntax/Parser.lean` calls `importModules` and `Meta.evalExpr` through
`unsafe` definitions, so a `fir-ref` built on it needs the `.olean` files at
run time and cannot be reasoned about. Its printer is a `partial def`, opaque
to proofs. So fir writes its own parser and printer either way. With
LeanMLIR, the parser must type-check while it parses, to build a
`Σ Γ, Com d Γ eff ts`, and the theorem is over dependent terms, with names
and locations kept outside them. With the own calculus, the parser builds
plain first-order syntax, validation is separate (as in the Wasm spec), and
the theorem is an induction over ordinary inductives.

**Soundness of the `fir-ref` modes (#14).** Proved in the spike, with no
`sorry`: `Prog.exhaustive_eq_sem` (within its budget, exhaustive mode returns
exactly the semantic set) and `Prog.scripted_mem_sem` (scripted mode returns
a member of it), in `spike/own/FirOwn/Prog.lean`, about 60 lines. They are
facts about the monad, not the terms, and the LeanMLIR prototype uses them
unchanged. The cost is the same on either side.

**Facts about one program.** Both prototypes prove the outcome set of the
`i2` sample by `decide`, and that the `xor` sample's run is one choice
followed by `b ^^^ b`, by `rfl`. The own prototype then proves every
behaviour returns 0 (`frozen_xor_zero`). The own proofs use only `propext`
and `Quot.sound`; the LeanMLIR ones also use `Classical.choice`, through
Mathlib.

**Type safety.** LeanMLIR's intrinsic typing makes ill-typed terms
unrepresentable inside a block. The CFG layer is checked at run time, so a
proof is needed there anyway. The own calculus needs a progress proof
(validated modules never get stuck), which is the "other simple property"
#11 already asks for.

**Verified rewrites (roadmap, M1).** LeanMLIR gives a real benefit here.
`spike/leanmlir/FirLeanMLIR/Rewrite.lean` states `add %x, %y` to
`add %y, %x` as a `PeepholeRewrite`, proves it with `simp_peephole` and a
two-line case split, applies it with `rewritePeepholeAt`, and gets
`denote_rewritePeepholeAt` (the block keeps its meaning) for free. Its
limits: a `PeepholeRewrite` relates two pure terms by equality
(`Transforms/Rewrite/Rewrite.lean`). A rewrite that involves `freeze` cannot
be stated, because `freeze` is impure, and rewrites that refine poison need
`⊑`, not `=`. LeanMLIR's InstCombine proofs state `⊑` theorems outside the
rewriter, with LLVM-specific tactics (`simp_alive_peephole`, `alive_auto`)
that live in the parent `SSA` package. `bv_decide` is part of Lean itself,
not LeanMLIR: it closed the same goals on v4.35.0 and on the nightly, so both
options have it.

## Dependency cost

- **Pinned to an old nightly.** LeanMLIR pins `nightly-2025-12-01`. The
  stable Lean today is v4.35.0, with v4.36.0-rc2 out. LeanMLIR bumped its
  toolchain 171 times in 2025, nearly daily, and not once since 2025-12-03.
- **Activity moved elsewhere.** The `LeanMLIR/` framework directory was
  split out on 2025-09-25 and last changed on 2025-12-03. Of the 70 commits
  in 2026, 56 touch `Blase`, a bit-vector decision procedure. The
  framework has no release tags; the repository's tags mark paper artefacts.
- **The subpackage is not self-contained.** `LeanMLIR.Dialects.LLVM.Semantics`
  imports `SSA.Projects.InstCombine`, which is in the parent package. As a
  `subDir` dependency, `import LeanMLIR` fails ("unknown module prefix
  'SSA'"). Only the framework modules (`LeanMLIR.Basic`) build alone.
- **It no longer resolves.** Mathlib's manifest at that nightly pins
  `lean4-cli` at `d9fc8ae`, which is no longer on any branch. `lake update`
  fails (git exit 128). The workaround, in every fresh clone and in CI, is
  `git fetch origin d9fc8ae…` inside `.lake/packages/Cli`.
- **No Mathlib cache.** `lake exe cache get` downloaded none of the 7675
  files it tried, from either Mathlib cache. About 920 Mathlib modules build from source: roughly three
  minutes for the library, and longer for an executable, which also compiles
  Mathlib to C. These are rough figures from a shared 24-core machine, not
  measurements.
- **Verso follows the pin.** Verso has a tag `nightly-2025-12-01`, so the
  page builds, but the spec's tooling stays on that Verso. Verso can show code
  from a project on another Lean version (its "example project" mode), but
  then the definitions live outside the literate document, which is not what
  P1 describes.
- **Licence.** Apache-2.0. Compatible with funk's MIT licence; vendoring it
  would carry its notice. Vendored files would also break the 20,000-byte
  budget (`Framework/Basic.lean` is 53 KB) unless the hook excluded them.

Keeping up means either staying on a frozen nightly or porting LeanMLIR to
each Lean release ourselves, which is a fork in all but name.

## Readability in Verso

The Verso page (`spike/doc/SpikeDoc.lean`) shows `freeze`, the op signature
and the `@add3` sample from both prototypes, elaborated in one document. It
builds and renders to HTML with Verso's `nightly-2025-12-01` tag. With both
frameworks loaded, `PoisonOr` is ambiguous, so the page qualifies the own
calculus's name; a real spec loads only one.

- The op semantics read the same on both sides. That is expected: the own
  calculus copies LeanMLIR's shape for them.
- The signature reads slightly worse on LeanMLIR: every op carries an effect
  kind and an empty region list, and terminators return the encoding type
  `ctl`.
- The sample reads much worse on LeanMLIR: `⟨1, rfl⟩` is "the variable two
  bindings up, with a proof of its type", and nothing in the term matches the
  names or locations of the text. The own calculus's term has the text's
  names, labels and `@N` locations.

A spec reader compares the formal rules with the text format, so the own
calculus serves P1 better.

## What adding the missing features to LeanMLIR would take

- **CFGs with block arguments:** a new region form in `Com` (blocks,
  terminators with successors and typed successor arguments, dominance-based
  contexts), a fuel-based denotation, and new versions of every lemma, the
  zipper, the rewriter, DCE and CSE. Upstream has not touched the framework
  since 2025-12-03.
- **Names and locations:** fields on `Expr` (or `Com`), and changes to
  matching, equality, printing and the EDSL.
- **A toolchain that moves:** port LeanMLIR and the Mathlib it needs to each
  Lean release, or vendor it and do so.
- **A fir parser:** needed in any case.

## What each answer means for #8, #10, #11 and #14

| Issue | Own calculus | LeanMLIR |
| --- | --- | --- |
| #8 spec | A `lean/` package with no dependencies, on a Lean release that has a matching Verso release. Abstract syntax in the extrinsic shape of `spike/own`. `Prog` and its set semantics are the general part of execution. | Per-block `Com` terms plus fir's CFG layer, or a fork of LeanMLIR. Names and locations in side tables. The toolchain ADR pins `nightly-2025-12-01`, Mathlib `nightly-testing`, the `lean4-cli` fetch workaround and a Mathlib build in CI. Verso stays at its matching tag. |
| #10 interpreter | A CFG walker generic over dialect and monad, as in `spike/own`. fir's own parser and printer. `fir-ref` is a plain Lean executable. | `Com.denote` inside blocks, plus the CFG layer. fir's own parser, which must type-check while it parses, and its own printer. `fir-ref` links Mathlib. |
| #11 proofs | Print-then-parse over first-order syntax. A progress theorem: validated modules never get stuck. | Print-then-parse over dependent terms, with side tables for names and locations. Blocks are well typed by construction; the CFG layer still needs a proof. |
| #14 `freeze` | The `Prog` handlers and both soundness proofs from the spike. | The same, unchanged. `freeze` is impure, so no `PeepholeRewrite` can involve it. |

## Recommendation

Define fir's own calculus, in the shape of LeanMLIR's typed SSA classes, with
no dependency beyond Lean itself. The proposed ADR says how close to stay.
LeanMLIR's real benefit, the verified rewriter, matters from M1 on, works only
on pure straight-line code, and can still be reached later by translating
fir blocks into LeanMLIR terms, because the per-op semantics have the same
type on both sides.

## How to reproduce

From the prototype branch, with `elan` installed:

```sh
cd spike/own && lake build           # samples, guards and proofs
cd ../leanmlir && lake update        # fails on lean4-cli d9fc8ae; then:
git -C .lake/packages/Cli fetch origin d9fc8ae23024be37424a189982c92356e37935c8
lake build                           # builds Mathlib from source
cd ../doc && lake update             # same lean4-cli workaround
lake build && lake exe spikedoc --output _out
```
