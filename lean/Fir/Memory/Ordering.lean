import Fir.Prelude

/-!
# The ordering of an access

Every load and store carries an ordering (ADR-2026-11-09-1542): how the
access is ordered with the accesses of other threads. M1 has one thread, and
its validation accepts only `nonatomic`, a plain access that no other thread
may race with. The other orderings are hooks in the format: they decode, so
a concurrency model (S6) can give them a meaning with no change of the
format, and validation rejects them until it does. The orderings are the
atomic orderings of LLVM and of C++, with LLVM's names: `unordered`,
`monotonic` (C++'s relaxed), `acquire`, `release`, `acq_rel` and
`seq_cst`. A rule with memory reads every ordering as `nonatomic`, since no
valid module carries another.
-/

namespace Fir.Memory

/-- The ordering of a load or a store (ADR-2026-11-09-1542). M1 accepts only
`nonatomic`; the others are hooks for a concurrency model. -/
inductive Ordering where
  | nonatomic
  | unordered
  | monotonic
  | acquire
  | release
  | acqRel
  | seqCst
  deriving Repr, DecidableEq

end Fir.Memory
