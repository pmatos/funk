# fir-ref tries a few NaNs at each NaN choice and lists a proved subset of the outcomes

Status: accepted
Tier: direction; area: fir-ref

## Decision

- **The NaN choice is labelled.** A float op whose result is a NaN chooses its
  sign and mantissa, `m + 1` bits, with `MonadChoice.chooseNaN e m`
  (ADR-2026-11-09-1549). In the set monad it is the choice of `m + 1` bits, so
  the semantics does not change. In the tree of choices its node carries the
  kind `ChoiceKind.nan e`; every other choice has the kind `bits`.
- **`fir-ref run --exhaustive --nans V,...`.** At a choice of bits it tries
  every value, as `--exhaustive` does. At a NaN choice of `float<e,m>` it
  tries the positive quiet NaN and each `V`, a bit pattern, that is a NaN of
  that format, and charges the budget the fewest bits that count them: none
  for the quiet NaN alone. `--exhaustive` without `--nans` is unchanged.
- **A subset, and the output says when.** Each outcome listed is an outcome
  of the spec's set (`Gpu.exhaustiveNaN_memOutcomes`). The result has
  `"complete":true` when no path made a NaN choice, and the list is then
  exactly the set (`Gpu.exhaustiveNaN_exact`); otherwise `"complete":false`.

The harness is to give the `V`s from native code's own results, so that a
native NaN is a listed outcome when a NaN choice can give it; #219 builds
that judgement.

## Why

A NaN of `f32` is 24 chosen bits and one of `f64` 53, past any budget, and
the choices compound across ops. #219 asks for a representation proved equal
to the spec's set or a sound approximation of it. A subset needs no new
semantics and is proved once for any tree, and a listed outcome is a proof of
membership.

It misses a NaN whose bits integer ops change before they reach a result,
and UB or a stuck path that only an untried payload reaches. Each `V` is
tried at every NaN choice, so the paths grow with the NaN choices on a path,
within the budget.

## Rejected alternatives

- **A symbolic "any NaN" outcome.** It is exact only while no op reads a
  NaN's bits, and `bitcast` and memory read them; it needs a symbolic
  interpreter proved against the spec.
- **Every wide choice tries a few values.** It would change the rule for
  `freeze` past the budget, where a test declares its results.
- **Both quiet NaNs by default.** Each NaN choice would cost a bit, and a
  loop of NaN ops would pass any budget.
