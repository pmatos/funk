import Fir.Core.Values

/-!
# Freeze

`freeze` stops poison (ADR-2026-10-29-2006). It gives its operand as it is
when the operand is not poison. When it is poison, it gives an arbitrary
value of its type, chosen once: the rule chooses N bits once, and the
interpreter binds the op's one result to the value it gives. Every use of
that result then sees the same bits, so `sub %f, %f` of a frozen poison
`%f` is 0. Another `freeze` of the same poison chooses again, and may give
other bits (ADR-2026-10-29-2017).

`freeze` is an exception to poison propagation, with this rule of its own
(ADR-2026-10-30-0818): its result is never poison. It is never UB. The rule
is written once, for every way of computing that can choose bits. In the
set of the ways a run may end, it gives every value of the type, and in
`fir-ref`'s tree of choices it is one choice of N bits.
-/

namespace Fir.Core

/-- `freeze` of a value of `iN`, with `N = w`: the value itself, or bits
chosen once when it is poison. -/
def freezeValue {m : Type → Type} [Monad m] [MonadChoice m] {w : Nat} :
    PoisonOr (BitVec w) → m (PoisonOr (BitVec w))
  | .value a => pure (.value a)
  | .poison => do
    let b ← MonadChoice.choose w
    pure (.value b)

end Fir.Core
