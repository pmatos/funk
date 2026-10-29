# fir's Lean semantics is its own calculus, in the shape of LeanMLIR's classes

Status: accepted

## Context

The human chose this on 2026-10-29, in PR
[#27](https://github.com/pmatos/funk/pull/27), after an independent check of
the spike's findings. The M0 epic's
[rulings comment](https://github.com/pmatos/funk/issues/5#issuecomment-6506908304)
records it.

The fir spec (#8) fixes the Lean types of fir's semantics, parameterized over
the dialect (G0, ADR-2026-10-29-2016). The spike in
[#24](https://github.com/pmatos/funk/issues/24) asked whether they should
build on LeanMLIR ([opencompl/lean-mlir](https://github.com/opencompl/lean-mlir)),
an intrinsically typed SSA framework in Lean, or be fir's own calculus. It
built the same piece of fir both ways. Its report,
[`docs/spikes/leanmlir.md`](../spikes/leanmlir.md), has the evidence. In
short:

- LeanMLIR's framework allows poison apart from UB (S1, ADR-2026-10-29-2006)
  and a choice effect for `freeze` (ADR-2026-10-29-2017).
- It has no CFG (H1, ADR-2026-10-29-2010), no op locations (H8,
  ADR-2026-10-29-2013) and no value names (P3, ADR-2026-10-29-2014). A CFG
  means changing the term that the whole framework is built on.
- Its parser and printer cannot serve fir, and its rewriter proves only
  equality of pure straight-line terms.
- It is frozen on Lean `nightly-2025-12-01`.

## Decision

fir's Lean semantics is its own calculus. It takes no dependency on LeanMLIR.

It keeps LeanMLIR's shape wherever that is cheap. That shape is the
typeclass style G0 asks for, and per-op semantics port between the two
mechanically:

- A dialect is a structure with `Op` and `Ty`. `TyDenote` gives each type its
  meaning, written `⟦t⟧`. `DialectSignature` gives each op its operand and
  result types, and later its region signatures and effect kind. Operands
  travel in an `HVector`.
- Each op's semantics has the shape of LeanMLIR's `DialectDenote.denote`:
  `(op : d.Op) → HVector toType (sig op) → m (HVector toType (returnTypes op))`.
  LeanMLIR's `denote` also takes the op's regions, and runs pure ops outside
  the dialect monad. A port adjusts for both.
- Values of `iN` are `PoisonOr (BitVec N)`, with `poison` and `value` named
  as in LeanMLIR. It is fir's own type, so a port converts between the two.
- `⊑` is written through a heterogeneous refinement class shaped like
  LeanMLIR's `HRefinement`. This fixes only the notation. #8 defines the
  relation, over outcome sets, as S4 (ADR-2026-10-29-2008) requires.

It differs from LeanMLIR on purpose in four places:

- Terms are extrinsically typed. Values have names, every op has a location,
  and a function is a CFG of blocks with arguments and successors. Typing is
  a separate validation judgement, as in the Wasm spec.
- Terminators are ops that `DialectSignature.isTerminator` marks. Their
  semantics is `DialectDenote.exit`, which returns an `Exit` (a successor
  index, or return). `Exit` may grow (H6, unwinding). LeanMLIR has no
  successors, so a port encodes them as ops that return a control value.
- A dialect does not fix one monad. Its semantics states the effects it needs
  as class constraints on the monad. The spike's subset needs `choose w` and
  immediate UB; calls (#20) add an effect that shares the fuel budget.
- The parser and printer are fir's own, over the extrinsic syntax.

The term carries op regions from M0 on, empty for core ops, as G0's single
grammar requires. Only region signatures and region semantics come later.
The CFG is the core dialect's region kind (E0, ADR-2026-10-29-2005).

The encoding admits sum or wrapper dialects, as LeanMLIR's `Scf` functor
does; #10's test-only toy dialect needs one. How extensions compose belongs
to H4 and H5.

## Alternatives

- **Depend on LeanMLIR.** A CFG layer outside the framework, with block
  arguments typed at run time and no access to dominating values; names and
  locations kept outside the terms; Lean frozen at `nightly-2025-12-01`; a
  fir parser needed anyway.
- **Fork LeanMLIR.** Add CFGs, names and locations to its core term, and port
  it and its Mathlib dependency to each Lean release ourselves. Its files
  also exceed the 20,000-byte budget (ADR-2026-10-28-0724).
- **Build on VeIR** ([opencompl/veir](https://github.com/opencompl/veir), read
  at [`35114775`](https://github.com/opencompl/veir/tree/351147753c4240e07e738bd79f1974e3141aaa1a)),
  the same group's active successor framework. It is on Lean `v4.35.0-rc4`
  with no Mathlib, and has CFGs with block arguments, refinement over poison,
  `freeze` as a choice, DCE and CSE, and refinement-based rewrite
  obligations. Rejected for now, because it conflicts with decided rows. Its
  interpreter uses coinductive choice trees, and S7 (ADR-2026-10-29-2009)
  says "not interaction trees". It stubs out locations (`Location := Unit`;
  H8). Its values have no names (P3). Its IR is a pointer graph, which fits
  neither the literate spec (P1, ADR-2026-10-29-2015) nor the round-trip
  proof (#11). S7 is the row the human would have to reopen to choose it.

## Consequences

- `lean/` is not tied to LeanMLIR's frozen nightly, so it can follow stable
  Lean and Verso releases. Its toolchain and dependencies, Mathlib included,
  are decided by #8's Lean toolchain ADR (P1, ADR-2026-10-29-2015).
- The print-then-parse theorem (#11) is an induction over plain inductives.
  Locations and names are part of the term.
- This ADR does not decide how #14 builds the choice effect. The spike ran
  its interpreter in `Prog`, an inductive free monad over `choose` and UB,
  and proved the `fir-ref` modes sound as handlers of it. #14 decides whether
  to keep that design. It checks it against S7 (ADR-2026-10-29-2009, "not
  interaction trees") and against ADR-2026-10-29-2017's "set instance of the
  monad": `Prog` is a finite tree, not a coinductive one, fuel still bounds
  runs, and its semantics is a handler, not a set instance.
- We prove type safety ourselves: a validated module never gets stuck.
- We give up LeanMLIR's rewriter, DCE, CSE and tactics. Verified rewrites
  (M1) mean fir's own refinement-based rewrite framework, or VeIR if S7 is
  reopened. A translation to LeanMLIR would first need LeanMLIR on fir's
  toolchain: it is frozen on `nightly-2025-12-01`, and its upstream toolchain
  bump has failed since 2025-12. `bv_decide` is part of Lean and stays
  available.
