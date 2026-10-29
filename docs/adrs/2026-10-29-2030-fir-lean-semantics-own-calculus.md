# fir's Lean semantics is its own calculus, in the shape of LeanMLIR's classes

Status: proposed

## Context

The fir spec (#8) fixes the Lean types of fir's semantics. Before it does, a
spike (#24) asked whether those types should build on LeanMLIR
([opencompl/lean-mlir](https://github.com/opencompl/lean-mlir)), an
intrinsically typed SSA framework in Lean, or be fir's own calculus. G0 asks
for a Lean semantics parameterized over the dialect.

The spike built the same piece of fir both ways. Its report is
[`docs/spikes/leanmlir.md`](../spikes/leanmlir.md). The facts that decide:

- LeanMLIR's framework allows what S1 and the `freeze` design need: poison as
  a value, UB and choice as effects of the dialect monad. Its refinement
  classes fit S4.
- It has no CFG (H1), no location on ops (H8) and no value names (P3). A
  region is one straight-line term. Adding them means changing the inductive
  that the whole framework is built on.
- Its parser runs Lean's elaborator at run time, and its printer is a
  `partial def`. fir needs its own parser and printer either way (#10, #11).
- Its rewriter proves pure, equality-preserving rewrites inside one block.
  That is useful from M1 on, but cannot state a rewrite that involves
  `freeze` or refines poison.
- It pins `nightly-2025-12-01`, unchanged since 2025-12-03. Its subpackage
  does not build alone, its dependencies no longer resolve without a manual
  fetch, and the Mathlib cache for that nightly is gone.

## Decision

fir's Lean semantics is its own calculus. It takes no dependency on LeanMLIR
or Mathlib, so it can follow stable Lean and Verso releases. (Verso is there
for P1; the P1 ADR says where the Verso document lives.)

It keeps LeanMLIR's shape wherever that is cheap, so that porting per-op
semantics between the two is mechanical:

- A dialect is a structure with `Op` and `Ty`. `TyDenote` gives each type its
  meaning, written `⟦t⟧`. `DialectSignature` gives each op its operand and
  result types (and later its regions and effect kind). Operands travel in an
  `HVector`.
- Each op's semantics has the shape of LeanMLIR's `DialectDenote.denote`:
  `(op : d.Op) → HVector toType (sig op) → m (HVector toType (returnTypes op))`.
  LeanMLIR's `denote` also takes the op's regions, and runs pure ops outside
  the dialect monad. A port adds the regions argument and drops the `pure`.
- Values of `iN` are `PoisonOr (BitVec N)`, with `poison` and `value` named
  as in LeanMLIR. It is fir's own type, so a port converts between the two.
- Refinement is written `⊑`, through a heterogeneous refinement class shaped
  like LeanMLIR's `HRefinement`.

It differs from LeanMLIR on purpose in four places:

- Terms are extrinsically typed. Values have names, every op has a location,
  and a function is a CFG of blocks with arguments and successors. Typing is
  a separate validation judgement, as in the Wasm spec.
- Terminators are ops that `DialectSignature.isTerminator` marks. Their
  semantics is `DialectDenote.exit`, which returns an `Exit` (a successor
  index, or return). LeanMLIR has no successors, so a port encodes them as
  ops that return a control value.
- A dialect does not fix one monad. Its ops state the effects they need as
  class constraints on the monad. The core dialect needs `choose w` and
  immediate UB.
- The parser and printer are fir's own, over the extrinsic syntax.

If a later milestone wants LeanMLIR's rewriter, it translates a block's pure
straight-line ops into a LeanMLIR term. The per-op semantics carry over
with the mechanical changes above.

## Alternatives

- **Depend on LeanMLIR.** A CFG layer outside the framework, with block
  arguments typed at run time and no access to dominating values; names and
  locations kept outside the terms; Lean frozen at `nightly-2025-12-01`; a
  fir parser needed anyway.
- **Fork LeanMLIR.** Add CFGs, names and locations to its core term, and port
  it and its Mathlib dependency to each Lean release ourselves. Its files
  also exceed the 20,000-byte budget (ADR-2026-10-28-0724).

## Consequences

- fir stays on stable Lean and current Verso, with no Mathlib.
- The print-then-parse theorem (#11) is an induction over plain inductives.
  Locations and names are part of the term.
- This ADR does not decide how #14 builds the choice effect. The spike ran
  its interpreter in `Prog`, an inductive free monad over `choose` and UB,
  and proved the `fir-ref` modes sound as handlers of it. #14 decides whether
  to keep that design, and checks it against S7 ("not interaction trees"):
  `Prog` is a finite tree, not a coinductive one, and fuel still bounds runs.
- We prove type safety ourselves: a validated module never gets stuck.
- We give up LeanMLIR's rewriter, DCE, CSE and tactics for now. Verified
  rewrites (M1) need our own framework or a translation to LeanMLIR.
  `bv_decide` is part of Lean and stays available.
