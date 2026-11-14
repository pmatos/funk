import Fir

/-!
Tests of the memory obligations: they reject a computation that has the
effect they say it does not have, and accept one that does not have it. In
the state layer over the set monad, with one memory of 8-bit units, an
allocation allocates, a store writes and a load reads. A load writes
nothing and allocates nothing, so a declaration of a load needs only a read
of its memory. An allocation writes no unit of the allocations that were
there. A copy of a unit to another unit of the same memory reads it, though
it gives no result: the rejected weaker form of _no read_ would accept it
(`docs/decisions/semantics-effects.md#soundness`).
`FirTest/MemoryStoreReads.lean` shows that a store
does not read its memory. Which op declares what is the dialect's: these
computations are the memory effect's own operations, not fir's ops.
-/

namespace FirTest.MemoryObligations

open Fir Fir.Memory

/-- The memories of these tests: one memory, of 8-bit units. -/
abbrev Mems := Memories Unit (fun _ => 8)

/-- The state layer over the set monad, on those memories. -/
abbrev M := StateT Mems SetM

/-- The memories with one live heap allocation of one unit, which is
poison. -/
def one : Mems := (Memories.empty.alloc () .heap 1 1).2

/-- A memory of the same allocations as `one`'s, whose unit holds the bits
`1`. -/
def oneBits : Memory 8 := ⟨[⟨.heap, 1, [.bits 1], true⟩]⟩

/-- The pointer to the unit of `one`'s allocation. -/
def p : Pointer := ⟨some 0, 0⟩

/-- An allocation allocates in its memory. -/
theorem alloc_allocates : ¬ AllocatesNot () (MonadMemory.alloc () .heap 1 1 : M Pointer) := by
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
    exact prefix_refl _
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

/-- An allocation writes no unit of the allocations that were there: the new
one follows them. -/
theorem alloc_writesNot (k : AllocKind) (n al : Nat) :
    WritesNot () (MonadMemory.alloc (m := M) () k n al) := by
  intro S a S' h
  cases h
  show (S.mem ()).contents <+: ((S.alloc () k n al).2.mem ()).contents
  rw [Memories.alloc_mem_self]
  exact ⟨[List.replicate n .poison], by simp [Memory.contents, Memory.alloc]⟩

/-- A memory with one live heap allocation of two units, both the bits
`0`. -/
def zeros : Memory 8 := ⟨[⟨.heap, 1, [.bits 0, .bits 0], true⟩]⟩

/-- A memory of the same allocations as `zeros`, whose first unit holds the
bits `1`. -/
def oneZero : Memory 8 := ⟨[⟨.heap, 1, [.bits 1, .bits 0], true⟩]⟩

/-- The memories whose one memory is `zeros`. -/
def two : Mems := (Memories.empty : Mems).set () zeros

/-- Copies the first unit of the allocation `0` to its second. -/
def copy : M Unit := do
  let us ← MonadMemory.load (m := M) () ⟨some 0, 0⟩ 1
  MonadMemory.store (m := M) () ⟨some 0, 1⟩ us

/-- A copy within a memory reads it: from `zeros` it leaves the second unit
`0`, and from `oneZero` it makes it `1`, which is neither `0` nor what
`oneZero` held there. -/
theorem copy_reads : ¬ ReadsNot () copy := by
  intro h
  obtain ⟨e', he', hm⟩ := h two oneZero (by decide) (.ok ((), two.set () zeros))
    (.inl ⟨([.bits 0], two), rfl, rfl⟩)
  rcases he' with ⟨⟨us, S₁⟩, h1, h2⟩ | ⟨r, h1, rfl⟩
  · cases h1
    cases h2
    exact absurd (hm.2.2 0 1) (by decide)
  · cases h1

end FirTest.MemoryObligations
