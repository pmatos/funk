/-!
# The rounding mode of an op

Every float op that rounds carries a rounding mode (ADR-2026-11-09-1549,
ADR-2026-11-11-1801): how its exact result is rounded to a value of its
format. The modes are IEEE 754's five rounding-direction attributes
(§4.3): `rne`, round to nearest with ties to even (roundTiesToEven);
`rna`, round to nearest with ties away from zero (roundTiesToAway); `rtp`,
toward positive infinity (roundTowardPositive); `rtn`, toward negative
infinity (roundTowardNegative); and `rtz`, toward zero (roundTowardZero).

M1's validation accepts only `rne`, the one mode that Lean's float model
computes (the human's ruling of 2026-11-15 on #229). The other modes are
hooks in the format: they decode, so a later milestone can give them a
meaning with no change of the format, and validation rejects them until it
does. A rule reads every mode as `rne`, since no valid module carries
another.
-/

namespace Fir.Core

/-- The rounding mode of an op that rounds (ADR-2026-11-11-1801). M1
accepts only `rne`; the others are hooks for later modes. -/
inductive RoundingMode where
  | rne
  | rna
  | rtp
  | rtn
  | rtz
  deriving Repr, DecidableEq, Inhabited

end Fir.Core
