# `fir-ref` runs implementations of the spec's functions that are proved equal to them and registered with `@[csimp]`

Status: accepted
Tier: direction; area: fir-ref

## Decision

- **A spec function on `fir-ref`'s path that takes stack per level of
  nesting, per list element, per step or per call gets an implementation
  proved equal to it.** The implementation is a loop whose recursive calls are
  all tail calls. It keeps what is left to do on an explicit stack of frames,
  and writes its output into one accumulator. It is defined by well-founded
  recursion on a measure of its frames: total, with no fuel.
- **Each is registered with `@[csimp] theorem : @specFn = @fastFn`.** No
  `sorry`, `partial`, `unsafe`, `implemented_by` or `native_decide`; the
  proofs use only `propext`, `Classical.choice` and `Quot.sound`, which the
  Lean build checks.
- **They live in `lean/FirRef/`.** The spec in `lean/Fir/` does not change for
  them, so the theorems about the spec's functions hold for what `fir-ref`
  runs. `FirRef.Fast` imports every module that registers such a theorem, so
  that code compiled after it calls the implementations.
- **Otherwise, a new fast path needs a case that is clearly too slow.** More
  than linear time is not enough on its own. A case that is clearly too slow is
  raised to the human, and a fast path for speed is a new performance ticket,
  which needs the human first (ADR-2026-11-06-0744). No fast path is added for
  memory alone.
- **The existing speed-only fast paths stay.**

## Why

fir has no nesting limit, so `fir-ref` must give a verdict on a text nested to
any depth without a stack overflow (ADR-2026-10-30-1549). The spec's readers,
decoder, printer and interpreter are readable recursive definitions, and the
proofs are about them. `@[csimp]` makes the compiler use the implementation
while proofs and the kernel still see the spec's function, so what `fir-ref`
computes is proved to be what the spec defines, byte for byte.

On 2026-11-05 the human ruled that Lean-side speed is not a concern: about 10x
of the Rust side is a rough guide, and hours on a simple example is not fine
([#5](https://github.com/pmatos/funk/issues/5#issuecomment-6506908304)). On
2026-11-09 the human ruled that `lean/FirRef` stays (#169): each fast path is
proved equal to the spec, so keeping one costs no trust, and none can go
without making `fir-ref` far slower.

## Rejected alternatives

- **Rewrite the spec's functions as loops.** The spec would lose its readable
  definitions, and its proofs would be about machines.
- **`implemented_by`.** It proves nothing: the compiled code could differ from
  the spec without any check failing.
- **A thread with a larger stack.** It moves the limit instead of removing it.
- **Keep "more than linear time" as a trigger.** It asks for speed work that
  the 2026-11-05 ruling says is not needed.
