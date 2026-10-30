# The axiom check allows proofs by native evaluation

Status: accepted

## Context

The axiom check of ADR-2026-10-30-1452 fails the build on any declaration in
`lean/` that depends on an axiom other than `propext`, `Classical.choice`
and `Quot.sound`. That rejected every proof by native evaluation:
`native_decide`, `decide +native`, and `bv_decide` when it uses native
evaluation.

Such a proof trusts Lean's compiler. On the toolchain that `lean/` pins
(v4.35), `Lean.Meta.nativeEqTrue` compiles a closed term `e : Bool`, runs it,
and, when it gives `true`, adds a new axiom `e = true`. That axiom is named
after the declaration, then `_native`, the tactic and `ax_…`, for example
`t._native.native_decide.ax_1_1`. Earlier toolchains used one global axiom,
`Lean.ofReduceBool`, instead.

The human ruled on 2026-10-30, in
[#52](https://github.com/pmatos/funk/issues/52), to trust the compiler. The
check allows native evaluation and keeps every other ban. A text check that
banned `native_decide` was proposed and then dropped.

## Decision

- The check accepts an axiom of native evaluation, wherever a declaration
  depends on it, and the axiom itself. An axiom counts as one only when all
  of these hold:
  - its name ends in `_native`, a tactic's name, and a part that starts with
    `ax_`;
  - its type is `e = true` for a closed term `e : Bool`;
  - the check compiles and runs `e` again with `Lean.Meta.nativeEqTrue` and
    gets `true`.
- Everything else stays banned in `lean/`: `sorry`, every other axiom,
  `unsafe`, `partial`, `implemented_by` and `@[extern]`. A `@[csimp]` swap
  stays allowed, because each one is proved.

## Consequences

- `lean/` may prove decidable facts by running them, which is faster than the
  kernel's `decide` on large instances.
- The trusted base grows by Lean's compiler and by the runtime that
  evaluates the compiled code. The bans on `unsafe`, `partial`,
  `implemented_by` and `@[extern]` keep the compiled code equal to the
  definitions that the proofs are about. So a
  native evaluation runs our proved definitions, and no code that the
  kernel cannot see.
- A hand-written axiom whose name only looks native still fails the check,
  unless its claim really evaluates to `true`.
- `#print axioms` lists one axiom per native proof, beside the standard
  three.
- A toolchain that changes how native evaluation is recorded (for example
  back to a single axiom such as `Lean.ofReduceBool`) needs the check updated
  in the same PR. Until then, the check rejects such proofs.
