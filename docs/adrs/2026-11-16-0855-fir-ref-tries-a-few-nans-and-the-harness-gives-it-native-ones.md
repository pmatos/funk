# fir-ref tries a few NaNs at each NaN choice, and the harness gives it native code's

Status: accepted
Tier: direction; area: fir-ref

## Decision

- **The NaN choice is labelled.** A float op whose result is a NaN chooses its
  sign and mantissa, `m + 1` bits, with `MonadChoice.chooseNaN e m`
  (ADR-2026-11-09-1549). In the set monad it is the choice of `m + 1` bits, so
  the semantics does not change. In the tree of choices its node carries the
  kind `ChoiceKind.nan e`, and every other choice, `freeze`'s and `nsz`'s,
  the kind `bits`.
- **`fir-ref run --exhaustive --nans V,...` tries a few NaNs.** At a choice of
  bits it tries every value, within the choice budget, as `--exhaustive`
  does. At a NaN choice of `float<e,m>` it tries the quiet NaN of each sign
  and each `V`, a bit pattern in hex, that is a NaN of that format, and it
  charges the budget the bits that count the NaNs it tries. `--exhaustive`
  without `--nans` is unchanged.
- **The set is a subset, and the output says when.** Each outcome listed is
  an outcome of the spec's set (`Gpu.exhaustiveNaN_memOutcomes`). The result
  has `"complete":true` when no path made a NaN choice, and the list is then
  exactly the set; otherwise `"complete":false`.
- **The harness judges by membership.** It gives `fir-ref` the bits of each
  value native code returned as the `V`s, and native code passes when its
  result refines a listed outcome. A pass is a proof that the result is in
  the set. A wrong value, a NaN where none is allowed included, is never
  listed, so it fails.

## Why

A NaN of `f32` is 24 chosen bits and one of `f64` 53, past any budget, and the
choices compound across ops. The issue (#219) asks for a representation proved
equal to the spec's set or a sound approximation of it. A subset needs no new
semantics and is proved for any tree; native code's own bits are the NaNs most
worth trying, since a NaN usually reaches a result unchanged.

The subset misses a NaN whose bits integer ops change before they reach a
result, and UB that only an untried payload reaches. A test with the first
declares its results; UB in a set allows any result, so missing it never
turns a wrong result into a pass.

## Rejected alternatives

- **A symbolic "any NaN" outcome.** It is exact only while no op reads a
  NaN's bits, and `bitcast` and memory read them; it needs a symbolic
  interpreter proved against the spec.
- **Every wide choice tries a few values.** It would change the rule for
  `freeze` past the budget, which declares its results.
- **Any native NaN matches any NaN.** It passes a wrong NaN where a constant
  or a `bitcast` gives exactly one.
