# The poison obligations cover only op instances whose types validation accepts

Status: accepted; refined by ADR-2026-11-05-1715

## Context

`LawfulDialectPoison` asked its obligations of every op instance,
including those at types that validation rejects. The core dialect's
validation rejects `i0`. At `i0`, `BitVec 0` has one value, so every
divisor is zero and every division is UB on every operand vector: no
division at `i0` returns a result on defined operands
(`Core.div_zero_width`, from
[PR #68](https://github.com/pmatos/funk/pull/68)). So `returnsOnDefined`
failed for `sdiv`, `udiv`, `srem` and `urem` at `i0`, and the core
dialect could not meet the class
([#69](https://github.com/pmatos/funk/issues/69)).

The spec had no generic notion of a valid op instance. Validation checks
an op in its place in a function (`Func.OpValid`), and a dialect's own
rule for an op (`validOp`) reads the op's context: the module's symbol
table and the function's result types.

The human ruled on 2026-11-02, on #69, to narrow the obligations to valid
instances. The orchestrator took the sub-choice that #69 recommended: the
whole class.

## Decision

- A generic notion, `TypesValid op`: each operand type and each result
  type of the op instance `op` is valid for its dialect (`validTy`)
  ([`lean/Fir/Validation/Rules.lean`](../../lean/Fir/Validation/Rules.lean)).
  It is the smallest one that the core dialect instantiates with its
  validation, `Core.Ty.Valid`: `iN` with `1 ≤ N ≤ maxWidth`, never `ptr`.
  It reads no context, so it is a property of the op instance alone.
- Every field of `LawfulDialectPoison` covers only such instances.
  `poison_isRefinedBy` speaks of valid types; `propagates`,
  `returnsOnDefined`, `total` and `monotone` of op instances that meet
  `TypesValid`.
- Every op of a valid function meets it (`Func.Valid.typesValid`). So the
  class still gives progress for every function of a valid module whose
  functions run within it (`Func.progress_of_lawful`); that no path is
  stuck needs no op property at all. No valid program changes meaning.
- Division at `i0` keeps its rule. `Core.div_zero_width` stays true, and
  is the reason for the narrowing.

This refines ADR-2026-10-30-0818, which asked the obligations of every op.

## Alternatives

- **Change division at width zero**, for example by making a zero divisor
  at `i0` not UB. It changes the rule of an instance that no valid module
  holds, only to make the class provable.
- **Narrow only `returnsOnDefined`.** The other fields hold at `i0` in the
  core dialect, but a field that speaks of instances that validation
  rejects constrains nothing that a valid program runs. Not taken: the
  whole class was the sub-choice #69 recommended and the orchestrator took
  under the ruling.
- **Ask `validOp` too.** It needs a context that an op instance alone does
  not have. Its rules, such as `zext` strictly widening, are checked by
  validation in each function, and no obligation needs them.

## Consequences

- `LawfulDialectPoison CoreDialect` holds (`Core.lawfulDialectPoison`).
- A dialect proves its obligations only for the instances that its
  validation accepts.
- The refinement engine (`Func.runs_args_isRefinedBy`,
  `Func.runs_replaceBody_isRefinedBy` and the theorems under them) asks
  monotonicity of every op that runs by its own rule, at every op
  instance, valid or not, not only at those of the modules it compares.
  The class covers only valid instances, so it does not give that by
  itself. The core dialect meets it with `Core.Op.monotone_all`, which
  holds at every width, `i0` included. So `Core.args_isRefinedBy` and
  `Core.replaceBody_isRefinedBy` keep their statements, and refinement
  holds for every core module.
- Nothing is lost against the spec before the narrowing. No theorem of
  the spec took the class as a hypothesis: the only use was a test's sum
  of two dialects, whose instance is built from its summands'. The core
  dialect had no instance. The class's `monotone` field had the type of
  the engine's hypothesis, so a lawful dialect met it in one line; now a
  dialect proves it at every instance itself, as the core dialect already
  did. M0 has only the core dialect.
- Asking monotonicity only of the ops of the modules the engine compares
  would let refinement follow from the class alone for every dialect. It
  would change these theorems' statements beyond the guard of
  ADR-2026-11-02-1514, which neither ruling asks for, so it is left open.
