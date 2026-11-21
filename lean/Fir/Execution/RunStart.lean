import Fir.Execution.MemoryObligations

/-!
# The memories a run starts with

Each global is one allocation of kind `global`, live for the whole run
(ADR-2026-11-09-1546). So a run does not start from empty memories: it
starts from memories that already hold the allocations that the items of
the run list (`RunItems.starts`), one for each global of its function's
table, outside every call. Each is the next allocation of the memory of
its number, in the order of the list, so in each memory the globals of
the table take the ids from 0 up, in the table's order, before anything the
run allocates. A global's units are its initializer's, followed by zeros up
to its size (the human's ruling of 2026-11-20 on #237, Q1). A constant
global's block is constant, so a store to it faults: writing a constant
global is UB when the write runs (Q2). A run holds the globals of its own
table only (Q3).

A run names the dialect's memories by `ρ`, and the dialect says which of
its memories a module's data layout numbers (`DialectEffects.numbered`):
the core's memory `n` is the memory numbered `n`, and a sum's are its
base's. An allocation in a memory the dialect does not number is left out,
so a dialect with no numbered memory starts from empty memories, as every
run did before globals.

Every run of the spec starts so: the runs with memory, the runs that see
the end of each return and the traced runs, under every address policy.
The obligations and guarantees over them hold for every record of the
items a run gives, so for every list of starting allocations, with no
hypothesis on it; their proofs already run from given memories.
-/

namespace Fir

open Memory

variable {N : Type} [DecidableEq N] {unit : N → Nat}

/-- The block that the starting allocation `a` gives in a memory of `u`-bit
units: live, with no address yet, of `a`'s kind, alignment, constness and
units. -/
def StartAlloc.block (a : StartAlloc) (u : Nat) : Memory.Block u :=
  ⟨a.kind, a.align, a.units u, true, none, a.const⟩

/-- The memories with the block `b` added to the memory `x`, as its next
allocation. -/
def Memory.Memories.place (S : Memories N unit) (x : N) (b : Memory.Block (unit x)) : Memories N unit :=
  S.set x ⟨(S.mem x).blocks ++ [b]⟩

/-- The memories that hold the starting allocations `as`, in order, each as
the next allocation of the memory that `ν` names for its number, outside
every call. An allocation of a number that `ν` names no memory for is left
out. -/
def Memory.Memories.ofStarts (unit : N → Nat) (ν : Nat → Option N) (as : List StartAlloc) :
    Memories N unit :=
  as.foldl (fun S a => match ν a.mem with
    | some x => S.place x (a.block (unit x))
    | none => S) Memories.empty

/-- The memories a run of the dialect `d` starts with, where a run names
its memory `x` as `ρ x`, whose layout entry is `lay (ρ x)`, and gives the
items `L`: the allocations of `L`, each in the memory of its number. -/
def RunItems.start (d : Dialect) [DialectEffects d] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem d → N) (L : RunItems) : Memories N (unitsOf lay) :=
  Memories.ofStarts (unitsOf lay) (fun n => (DialectEffects.numbered (d := d) n).map ρ) L.starts

/-- Placing a block keeps the frames. -/
theorem Memory.Memories.place_frames (S : Memories N unit) (x : N) (b : Memory.Block (unit x)) :
    (S.place x b).frames = S.frames := rfl

/-- The starting memories are outside every call: they have no frame. -/
theorem Memory.Memories.ofStarts_frames (ν : Nat → Option N) (as : List StartAlloc) :
    (Memories.ofStarts unit ν as).frames = [] := by
  unfold Memories.ofStarts
  suffices ∀ (S : Memories N unit), S.frames = [] →
      (as.foldl (fun S a => match ν a.mem with
        | some x => S.place x (a.block (unit x))
        | none => S) S).frames = [] from this _ rfl
  induction as with
  | nil => exact fun _ h => h
  | cons a as ih =>
    intro S h
    apply ih
    simp only
    split <;> exact h

/-- Allocations of numbers that name no memory leave the memories empty. -/
theorem Memory.Memories.ofStarts_none {ν : Nat → Option N} (h : ∀ n, ν n = none)
    (as : List StartAlloc) : Memories.ofStarts unit ν as = Memories.empty := by
  unfold Memories.ofStarts
  simp only [h]
  induction as with
  | nil => rfl
  | cons a as ih => exact ih

/-- A run of a dialect with no numbered memory starts from the empty
memories. -/
theorem RunItems.start_unnumbered (d : Dialect) [DialectEffects d] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem d → N) (L : RunItems)
    (h : ∀ n, DialectEffects.numbered (d := d) n = none) :
    RunItems.start d lay ρ L = Memories.empty :=
  Memories.ofStarts_none (fun n => by simp [h n]) _

/-- A run of items that list no allocation starts from the empty
memories. -/
theorem RunItems.start_nil (d : Dialect) [DialectEffects d] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem d → N) {L : RunItems} (h : L.starts = []) :
    RunItems.start d lay ρ L = Memories.empty := by
  simp [RunItems.start, Memories.ofStarts, h]

/-- An address policy changes no starting allocation. -/
@[simp] theorem RunItems.start_withAddrs (d : Dialect) [DialectEffects d] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem d → N) (L : RunItems) (g : Nat → Policy) :
    RunItems.start d lay ρ (L.withAddrs g) = RunItems.start d lay ρ L := rfl

omit [DecidableEq N] in
/-- A global starts with as many units as its size. -/
theorem Global.start_units_length (l : DataLayout) (gs : List Global) (g : Global) (u : Nat) :
    ((g.start l gs).units u).length = g.size := by
  simp only [Global.start, List.length_append, List.length_take, List.length_replicate]
  omega

end Fir
