import Fir.Execution.Frame
import Fir.Memory.Frames
import Fir.Memory.Resolver

/-!
# The memory effect

Memory is an effect of a run, beside choice and UB: an op that loads, stores
or allocates asks the run for it, as `freeze` asks for a choice of bits. A
dialect whose ops touch memory states its semantics in a monad that has the
memory effect, and any way of running a program that provides it can run
those ops (ADR-2026-10-29-2009).

The memory effect gives six operations of the memory model on the
memories of a run, each named by its memory: allocating, freeing, loading,
storing, exposing, and turning an integer back into a pointer. A load or a
store is an aligned access: it carries the alignment that the op promises,
in units. An access that faults is
immediate UB, for the reason of its fault, a misaligned access included
(ADR-2026-11-09-1542; the human's ruling of 2026-11-11 on #231). Exposing a
pointer turns it into an integer of the memory's pointer width, and gives
its allocation an address if it has none, under the address policy that the
op passes from its run (the section on address policies). When no address
may be given, it is immediate UB (the human's ruling of 2026-11-18 on #232,
Q5). Turning an integer back into a pointer picks an allocation that holds
its address under the resolver that the op passes from its run, which sees
how many integers the run has turned back into pointers before (the section
on address resolvers; the human's ruling of 2026-11-20 on #232, question
A). It never fails: with no allocation, the pointer has no provenance. The
frames of calls are the frame effect's (the section on the frame
effect), which an op never asks for. The state layer of the next section
adds the memories of a run to a monad with no memory, and gives both
effects.
-/

namespace Fir

open Memory

/-- The memory effect, on memories named by `Mem` whose units are `unit x`
bits wide for the memory `x`: six operations of the memory model. A
load or a store is aligned to a number of units, and one that faults,
misaligned or not, is immediate UB. Exposing is UB when no address may be
given. Turning an integer back into a pointer never fails. -/
class MonadMemory (Mem : outParam Type) (unit : outParam (Mem → Nat)) (m : Type → Type) where
  /-- Allocates `n` units of the kind `k`, aligned to `al` units, in the
  memory `x`, and gives the pointer to the first one. -/
  alloc : (x : Mem) → (k : AllocKind) → (n al : Nat) → m Pointer
  /-- Frees the allocation `a` of the memory `x`. -/
  free : (x : Mem) → (a : AllocId) → m Unit
  /-- Loads `n` units of the memory `x` through `p`, an access aligned to
  `al` units. -/
  load : (x : Mem) → (p : Pointer) → (n al : Nat) → m (List (MemUnit (unit x)))
  /-- Stores the units `us` to the memory `x` through `p`, an access aligned
  to `al` units. -/
  store : (x : Mem) → (p : Pointer) → (us : List (MemUnit (unit x))) → (al : Nat) → m Unit
  /-- Exposes the pointer `p` of the memory `x`, whose pointers are `P`
  bits wide, under the address policy `g`: its allocation's address plus
  its offset, wrapped at `P` bits. -/
  expose : (x : Mem) → (g : Policy) → (P : Nat) → (p : Pointer) → m (BitVec P)
  /-- Turns the integer `i` of the memory `x`, whose pointers are `P` bits
  wide, back into a pointer under the resolver `k`: of an allocation that
  holds its address, or with no provenance when none does. -/
  fromAddr : (x : Mem) → (k : Resolver) → (P : Nat) → (i : BitVec P) → m Pointer

end Fir
