import Fir

/-!
Tests of `alloca`'s rule with memory, run in the state layer over the tree
of choices, the monad that `fir-ref run` computes in: each allocation gets
the next id and a pointer at offset 0, takes its count times the units of
its type at the type's natural alignment or the op's own, and records a
stack allocation in the innermost frame, which frees it when the call
returns. An allocation in one memory leaves every other one as it was.
Then the axioms of the obligations that `alloca` meets with memory.
-/

namespace FirTest.Alloca

open Fir Fir.Core Fir.Memory

/-- Every memory of these runs has the default entry: 8-bit units and
64-bit pointers. The run names the core's memory `x` as `x`. -/
def lay : Nat → MemLayout := fun _ => MemLayout.default

abbrev Mems := Memories Nat (unitsOf lay)

abbrev M := StateT Mems (ChoiceTree Op)

/-- The pointer and the memories that one path of `c` from `S` ends with,
when it ends with a result. -/
def runOn (c : M (HVector toType [Ty.ptr n])) (S : Mems) : Option (Pointer × Mems) :=
  match c S with
  | .pure (.cons (.value p) .nil, S') => some (p, S')
  | _ => none

/-- `alloca k t c a n` from the memories `S`. -/
def alloca (k : AllocKind) (t : Ty) (c : Nat) (a : Option Nat) (n : Nat) (S : Mems) :
    Option (Pointer × Mems) :=
  runOn (allocaRule lay id k t c a n) S

/-- The shape of each block of memory `x`: kind, alignment, units, live. -/
def shapes (S : Mems) (x : Nat) : List (AllocKind × Nat × Nat × Bool) :=
  (S.mem x).blocks.map Block.shape

/-- Inside a call, four `i32`, then twelve `i8` aligned to 4, in memory 0. -/
def twice : Option (Pointer × Pointer × Mems) := do
  let (p, S) ← alloca .stack (.int 32) 4 none 0 Memories.empty.enter
  let (q, S) ← alloca .stack (.int 8) 12 (some 4) 0 S
  pure (p, q, S)

-- Each allocation gets the next id, and a pointer at offset 0.
#guard (twice.map fun (p, q, _) => (p, q)) == some (⟨some 0, 0⟩, ⟨some 1, 0⟩)

-- Four `i32` take 16 units aligned to 4; twelve `i8` aligned to 4 take 12.
#guard (twice.map fun (_, _, S) => shapes S 0) ==
  some [(.stack, 4, 16, true), (.stack, 4, 12, true)]

-- Both are recorded in the innermost frame, the later one first.
#guard (twice.map fun (_, _, S) => S.frames) == some [[(0, 1), (0, 0)]]

-- Leaving the call frees both and pops the frame.
#guard (twice.map fun (_, _, S) => (shapes S.exit 0, S.exit.frames)) ==
  some ([(.stack, 4, 16, false), (.stack, 4, 12, false)], [])

-- A callee's frame frees only its own allocations: the caller's stays live.
#guard (do
    let (_, S) ← alloca .stack (.int 32) 1 none 0 Memories.empty.enter
    let (_, S) ← alloca .stack (.int 64) 2 none 0 S.enter
    pure (shapes S.exit 0)) ==
  some [(.stack, 4, 4, true), (.stack, 8, 16, false)]

-- The natural alignment of `iN` in memory 0 is the least power of two that
-- is at least its units: 1 for `i1` and `i8`, 4 for `i24` and `i32`, 8 for
-- `i64` and 16 for `i128` (the human's ruling of 2026-11-14 on #378).
#guard [1, 8, 24, 32, 64, 128].map (fun w =>
    (alloca .stack (.int w) 1 none 0 Memories.empty.enter).map fun r => shapes r.2 0) ==
  ([(1, 1), (1, 1), (3, 4), (4, 4), (8, 8), (16, 16)] : List (Nat × Nat)).map fun (u, a) =>
    some [(AllocKind.stack, a, u, true)]

-- An alignment of the op's own replaces the natural one, and a count of 0
-- allocates no units, though validation rejects it.
#guard ((alloca .stack (.int 32) 1 (some 16) 0 Memories.empty.enter).map fun (_, S) =>
    shapes S 0) == some [(.stack, 16, 4, true)]
#guard ((alloca .stack (.int 32) 0 none 0 Memories.empty.enter).map fun (_, S) =>
    shapes S 0) == some [(.stack, 4, 0, true)]

-- A pointer element takes the units of its memory's pointers: 8 in memory 0.
#guard ((alloca .stack (.ptr 0) 2 none 0 Memories.empty.enter).map fun (_, S) =>
    shapes S 0) == some [(.stack, 8, 16, true)]

-- An allocation in memory 1 gets its own first id, and leaves memory 0 as it
-- was.
#guard (do
    let (_, S) ← alloca .stack (.int 32) 1 none 0 Memories.empty.enter
    let (q, S) ← alloca .stack (.int 8) 3 none 1 S
    pure (q, shapes S 0, shapes S 1, S.frames)) ==
  some (⟨some 0, 0⟩, [(.stack, 4, 4, true)], [(.stack, 1, 3, true)], [[(1, 0), (0, 0)]])

-- A heap allocation, which validation rejects in M1, is recorded in no
-- frame, so leaving the call keeps it live.
#guard (do
    let (_, S) ← alloca .heap (.int 32) 1 none 0 Memories.empty.enter
    pure (S.frames, shapes S.exit 0)) ==
  some ([[]], [(.heap, 4, 4, true)])

/-! # Axioms -/

/-- info: 'Fir.Core.alloca_memTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.alloca_memTotal

/-- info: 'Fir.Core.alloca_memMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.alloca_memMonotone

/-- info: 'Fir.Core.alloca_readsNot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.alloca_readsNot

end FirTest.Alloca
