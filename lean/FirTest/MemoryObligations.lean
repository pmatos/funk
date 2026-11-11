import Fir

/-!
Tests of the memory obligations: they reject a computation that has the
effect they say it does not have. In the state layer over the set monad,
with one memory of 8-bit units, an allocation allocates, a store writes and
a load reads. A load writes nothing and allocates nothing, so a declaration
of a load needs only a read of its memory. Which op declares what is the
dialect's: these computations are the memory effect's own operations, not
fir's ops.
-/

namespace FirTest.MemoryObligations

open Fir Fir.Memory

/-- The memories of these tests: one memory, of 8-bit units. -/
abbrev Mems := Memories Unit (fun _ => 8)

/-- The state layer over the set monad, on those memories. -/
abbrev M := StateT Mems SetM

/-- The memories with one live heap allocation of one unit, which is
poison. -/
def one : Mems := (Memories.empty.alloc () .heap 1).2

/-- A memory of the same allocations as `one`'s, whose unit holds the bits
`1`. -/
def oneBits : Memory 8 := ⟨[⟨.heap, [.bits 1], true⟩]⟩

/-- The pointer to the unit of `one`'s allocation. -/
def p : Pointer := ⟨some 0, 0⟩

/-- An allocation allocates in its memory. -/
theorem alloc_allocates : ¬ AllocatesNot () (MonadMemory.alloc () .heap 1 : M Pointer) := by
  intro h
  exact absurd (h Memories.empty _ _ rfl).1 (by decide)

/-- A store writes its memory. -/
theorem store_writes : ¬ WritesNot () (MonadMemory.store () p [.bits 1] : M Unit) := by
  intro h
  exact absurd (h one () (one.set () oneBits) rfl) (by decide)

/-- A load reads its memory: from `one` and from `one` with its memory
replaced by `oneBits`, it gives different units. -/
theorem load_reads : ¬ ReadsNot () (MonadMemory.load (m := M) () p 1) := by
  intro h
  obtain ⟨e', he', hm⟩ := h one oneBits (by decide) (.ok ([.poison], one)) rfl
  obtain rfl : e' = .ok ([.bits 1], one.set () oneBits) := he'
  exact absurd hm.1 (by decide)

/-- A load writes no memory: a path that ends keeps the memories. -/
theorem load_writesNot : WritesNot () (MonadMemory.load (m := M) () p 1) := by
  intro S a S' h
  simp only [MonadMemory.load] at h
  revert h
  cases S.load () p 1 with
  | ok us =>
    rintro ⟨⟩
    exact ⟨[], append_nil _⟩
  | error f => rintro ⟨⟩

/-- A load allocates in no memory: a path that ends keeps the memories. -/
theorem load_allocatesNot : AllocatesNot () (MonadMemory.load (m := M) () p 1) := by
  intro S a S' h
  simp only [MonadMemory.load] at h
  revert h
  cases S.load () p 1 with
  | ok us =>
    rintro ⟨⟩
    exact ⟨rfl, rfl⟩
  | error f => rintro ⟨⟩

end FirTest.MemoryObligations
