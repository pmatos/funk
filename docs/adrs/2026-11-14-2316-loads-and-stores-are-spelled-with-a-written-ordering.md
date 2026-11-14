# Loads and stores write their ordering, then their alignment when given

Status: accepted
Tier: direction; area: semantics

## Decision

- **The load.** `%v: iW = load ORDERING [align(A)] %p`, for example
  `%v: i32 = load nonatomic align(4) %p`. It has one operand, the pointer,
  and one result. Its memory is its pointer's.
- **The store.** `store ORDERING [align(A)] %v, %p`, with no result, the
  value before the pointer, its memory the pointer's (stage 4e-3 of #231).
- **The attributes.** The ordering is always written, then `align(A)` only
  when the op gives an alignment, separated by spaces as every op's
  attributes are, so each instance has one spelling. With no `align(A)` the
  access is aligned to the natural alignment of its type in its memory
  (`MemLayout.intAlign`).
- **The orderings.** The words are LLVM's: `nonatomic`, `unordered`,
  `monotonic`, `acquire`, `release`, `acq_rel` and `seq_cst`
  (`Memory.Ordering` in `lean/Fir/Memory/Ordering.lean`). Every one decodes;
  validation in M1 accepts `nonatomic` alone, so the others are hooks for a
  concurrency model (ADR-2026-11-09-1542). `A` is valid as `alloca`'s is: a
  power of two no larger than `MemLayout.limit`.

## Why

ADR-2026-11-09-1542 gives memory ops a written ordering, with `nonatomic`
alone in M1, so that a concurrency model (S6) needs no format change. The
human ruled on 2026-11-11 (#231, Q4) that loads and stores carry an
alignment that defaults to the type's natural alignment, and on 2026-11-14
(#382) that every op's attributes are separated by spaces. LLVM's ordering
words are the set that C11, C++11 and LLVM-based code already lower to, so
a front end maps its orderings one to one. The words are an agent's
proposal, put to the human on #391, the PR that adds `load`; this ADR is
edited in place if the human rules otherwise.

## Rejected alternatives

- **An optional ordering, `nonatomic` when omitted:** a nonatomic load
  would have two spellings, and a reader could not tell a forgotten ordering
  from a chosen one.
- **The C++ words (`relaxed`, `acq_rel`, `seq_cst`):** `relaxed` is
  LLVM's `monotonic`, and C++ has no `unordered`, which Java-style memory
  models need.
- **The pointer before the value in a store:** LLVM writes the value first,
  and so does every front end that lowers to it.
