import Fir.Memory.Refine

/-!
# Pointers under a renaming

At a return, an observer sees the returned values and the memory reachable
from them and from what escaped (ADR-2026-11-09-1540). The source and the
target of a pass number their allocations each in its own order, so two
ends of a run are compared up to a one-to-one _renaming_ of allocations: it
maps each allocation of the source that the observer sees to the target's
allocation in its place. Raw allocation ids are never compared.

A pointer of the source is seen in the target under a renaming as follows:

* a pointer with no provenance is seen as itself;
* a _dangling_ pointer, into an allocation of the source that is freed, is
  poison in the comparison, wherever the source has it (the human's rulings
  of 2026-11-15 on #309 and #233): no program can use it without UB, so any
  value of the target refines it;
* any other pointer is seen with its allocation renamed and its offset kept.
  An allocation that the source never made is renamed too, to one that the
  target never made (the section on the end of a run).

The renaming acts on every value that may hold pointers: on a returned
value, by its dialect (`HasPtrs` below), and on a unit of memory, whose
fragment of a pointer holds the pointer and the number of its memory. The
run names the memory of each number `n` as `μ n`.
-/

namespace Fir

open Memory

/-! # Renamings -/

/-- A renaming of allocations: for each memory, the allocation of the target
that an allocation of the source is renamed to, if it is renamed. -/
def Renaming (Mem : Type) : Type := Mem → AllocId → Option AllocId

namespace Renaming

variable {Mem : Type}

/-- A renaming is one-to-one when no two allocations of a memory are renamed
to the same one. -/
def Injective (R : Renaming Mem) : Prop :=
  ∀ x a b c, R x a = some c → R x b = some c → a = b

/-- The renaming that renames every allocation to itself. -/
protected def id : Renaming Mem := fun _ a => some a

/-- The renaming `R₁`, then `R₂`. -/
def comp (R₁ R₂ : Renaming Mem) : Renaming Mem := fun x a => (R₁ x a).bind (R₂ x)

/-- The renaming of every allocation to itself is one-to-one. -/
theorem id_injective : (Renaming.id : Renaming Mem).Injective := by
  intro _ _ _ _ h₁ h₂
  cases h₁
  cases h₂
  rfl

/-- One renaming then another is one-to-one when both are. -/
theorem Injective.comp {R₁ R₂ : Renaming Mem} (h₁ : R₁.Injective) (h₂ : R₂.Injective) :
    (R₁.comp R₂).Injective := by
  intro x a b c ha hb
  simp only [Renaming.comp, Option.bind_eq_some_iff] at ha hb
  obtain ⟨a', ha', ha''⟩ := ha
  obtain ⟨b', hb', hb''⟩ := hb
  exact h₁ x a b a' ha' (h₂ x b' a' c hb'' ha'' ▸ hb')

end Renaming

/-! # Dangling pointers -/

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- The memory `x` of the memories `S` has the allocation `a`, and it is
freed: a pointer into it is dangling. -/
def Memory.Memories.freed (S : Memories Mem unit) (x : Mem) (a : AllocId) : Bool :=
  match (S.mem x).blocks[a]? with
  | some b => !b.live
  | none => false

/-- How the target should show a pointer of the memory numbered `n` of the
source, whose memories are `S`, under the renaming `R`: a pointer with no
provenance as itself, a dangling one as poison (`none`), and any other with
its allocation renamed, when `R` renames it. -/
def Renaming.ptr (μ : Nat → Mem) (S : Memories Mem unit) (R : Renaming Mem) (n : Nat)
    (p : Pointer) : Option Pointer :=
  match p.prov with
  | none => some p
  | some a => if S.freed (μ n) a then none else (R (μ n) a).map fun a' => { p with prov := some a' }

/-- The renaming `R` renames the pointer `p` of the memory numbered `n`
unless it has no provenance or is dangling in `S`. -/
def Renaming.Covers (μ : Nat → Mem) (S : Memories Mem unit) (R : Renaming Mem) (n : Nat)
    (p : Pointer) : Prop :=
  ∀ a, p.prov = some a → S.freed (μ n) a = false → (R (μ n) a).isSome

/-! # Values that hold pointers -/

/-- A type of values that may hold pointers: the pointers a value holds,
each with the number of its memory, and the value with each pointer `p` of
the memory `n` replaced by `f n p`, or by poison when that is `none`. The
laws say that this replacement acts on the pointers alone, as poison does
elsewhere. -/
class HasPtrs (V : Type) [HRefinement V V] where
  /-- The pointers the value holds, each with the number of its memory. -/
  ptrs : V → List (Nat × Pointer)
  /-- The value with its pointers replaced. -/
  map : (Nat → Pointer → Option Pointer) → V → V
  /-- Replacing each pointer by itself changes nothing. -/
  map_some : ∀ v, map (fun _ p => some p) v = v
  /-- Two replacements in turn are one. -/
  map_map : ∀ f g v, map g (map f v) = map (fun n p => (f n p).bind (g n)) v
  /-- Replacing keeps refinement. -/
  map_mono : ∀ f {a b : V}, a ⊑ b → map f a ⊑ map f b
  /-- Replacing more of the value's pointers by poison refines less. -/
  map_le : ∀ f g v, (∀ n p, (n, p) ∈ ptrs v → f n p = none ∨ f n p = g n p) → map f v ⊑ map g v
  /-- A pointer that a replacement keeps, as `q`, is in each value that
  refines the result. -/
  ptrs_le : ∀ f {a b : V} {n p q}, map f a ⊑ b → (n, p) ∈ ptrs a → f n p = some q →
    (n, q) ∈ ptrs b

/-- A unit holds the pointer of its fragment, if it is one. -/
def Memory.MemUnit.ptrs {u : Nat} : MemUnit u → List (Nat × Pointer)
  | .frag m p _ => [(m, p)]
  | _ => []

/-- A unit with the pointer of its fragment replaced, or poison. -/
def Memory.MemUnit.mapPtr {u : Nat} (f : Nat → Pointer → Option Pointer) : MemUnit u → MemUnit u
  | .frag m p i => match f m p with
    | some q => .frag m q i
    | none => .poison
  | v => v

/-- A unit of memory holds the pointer of its fragment. -/
instance {u : Nat} : HasPtrs (MemUnit u) where
  ptrs := MemUnit.ptrs
  map := MemUnit.mapPtr
  map_some v := by cases v <;> rfl
  map_map f g v := by
    cases v with
    | frag m p i => cases h : f m p <;> simp [MemUnit.mapPtr, h]
    | _ => rfl
  map_mono f a b h := by
    cases a with
    | poison => exact trivial
    | bits _ => cases (h : b = _); exact MemUnit.isRefinedBy_refl _
    | frag _ _ _ => cases (h : b = _); exact MemUnit.isRefinedBy_refl _
  map_le f g v h := by
    cases v with
    | frag m p i =>
      rcases h m p (List.mem_singleton_self _) with hf | hf
      · simp only [MemUnit.mapPtr, hf]
        exact trivial
      · simp only [MemUnit.mapPtr, hf]
        exact MemUnit.isRefinedBy_refl _
    | _ => exact MemUnit.isRefinedBy_refl _
  ptrs_le f a b n p q h hp hq := by
    cases a with
    | frag m p' i =>
      simp only [MemUnit.ptrs, List.mem_singleton, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      simp only [MemUnit.mapPtr, hq] at h
      cases (h : b = _)
      exact List.mem_singleton_self _
    | _ => cases hp

/-- A list holds the pointers of its elements. -/
instance {V : Type} [HRefinement V V] [HasPtrs V] : HasPtrs (List V) where
  ptrs l := l.flatMap HasPtrs.ptrs
  map f l := l.map (HasPtrs.map f)
  map_some l := by
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons, HasPtrs.map_some]; exact congrArg _ ih
  map_map f g l := by
    simp only [List.map_map]
    exact List.map_congr_left fun v _ => HasPtrs.map_map f g v
  map_mono f a b h := by
    induction a generalizing b with
    | nil => cases b with
      | nil => exact trivial
      | cons _ _ => exact (h : False).elim
    | cons x a ih => cases b with
      | nil => exact (h : False).elim
      | cons y b => exact ⟨HasPtrs.map_mono f h.1, ih _ h.2⟩
  map_le f g l h := by
    induction l with
    | nil => exact trivial
    | cons x l ih =>
      refine ⟨HasPtrs.map_le f g x fun n p hp => h n p ?_, ih fun n p hp => h n p ?_⟩
      · exact List.mem_flatMap.2 ⟨x, List.mem_cons_self .., hp⟩
      · obtain ⟨y, hy, hp⟩ := List.mem_flatMap.1 hp
        exact List.mem_flatMap.2 ⟨y, List.mem_cons_of_mem _ hy, hp⟩
  ptrs_le f a b n p q h hp hq := by
    induction a generalizing b with
    | nil => cases hp
    | cons x a ih => cases b with
      | nil => exact (h : False).elim
      | cons y b =>
        obtain ⟨z, hz, hpz⟩ := List.mem_flatMap.1 hp
        rcases List.mem_cons.1 hz with rfl | hz
        · exact List.mem_flatMap.2 ⟨y, List.mem_cons_self .., HasPtrs.ptrs_le f h.1 hpz hq⟩
        · obtain ⟨w, hw, hq'⟩ := List.mem_flatMap.1 (ih _ h.2 (List.mem_flatMap.2 ⟨z, hz, hpz⟩))
          exact List.mem_flatMap.2 ⟨w, List.mem_cons_of_mem _ hw, hq'⟩

/-! # A dialect's values -/

/-- How the values of each type of a dialect hold pointers: `HasPtrs` for
the values of each type, with their refinement. -/
class TyPointers (Ty : Type) [TyDenote Ty] [TyRefinement Ty] where
  /-- The pointers a value holds, each with the number of its memory. -/
  ptrs : {t : Ty} → ⟦t⟧ → List (Nat × Pointer)
  /-- The value with its pointers replaced. -/
  map : (Nat → Pointer → Option Pointer) → {t : Ty} → ⟦t⟧ → ⟦t⟧
  map_some : ∀ {t : Ty} (v : ⟦t⟧), map (fun _ p => some p) v = v
  map_map : ∀ f g {t : Ty} (v : ⟦t⟧), map g (map f v) = map (fun n p => (f n p).bind (g n)) v
  map_mono : ∀ f {t : Ty} {a b : ⟦t⟧}, TyRefinement.IsRefinedBy a b →
    TyRefinement.IsRefinedBy (map f a) (map f b)
  map_le : ∀ f g {t : Ty} (v : ⟦t⟧), (∀ n p, (n, p) ∈ ptrs v → f n p = none ∨ f n p = g n p) →
    TyRefinement.IsRefinedBy (map f v) (map g v)
  ptrs_le : ∀ f {t : Ty} {a b : ⟦t⟧} {n p q}, TyRefinement.IsRefinedBy (map f a) b →
    (n, p) ∈ ptrs a → f n p = some q → (n, q) ∈ ptrs b

/-- A typed value holds the pointers of its value. -/
instance instHasPtrsDVal {d : Dialect} [TyDenote d.Ty] [TyRefinement d.Ty] [TyPointers d.Ty] :
    HasPtrs (DVal d) where
  ptrs v := TyPointers.ptrs v.2
  map f v := ⟨v.1, TyPointers.map f v.2⟩
  map_some v := by cases v; simp only [TyPointers.map_some]
  map_map f g v := by cases v; simp only [TyPointers.map_map]
  map_mono f a b h := by
    obtain ⟨t, a⟩ := a
    obtain ⟨t', b⟩ := b
    obtain ⟨h₁, h⟩ := h
    cases h₁
    exact ⟨rfl, TyPointers.map_mono f h⟩
  map_le f g v h := by
    obtain ⟨t, v⟩ := v
    exact ⟨rfl, TyPointers.map_le f g v h⟩
  ptrs_le f a b n p q h hp hq := by
    obtain ⟨t, a⟩ := a
    obtain ⟨t', b⟩ := b
    obtain ⟨h₁, h⟩ := h
    cases h₁
    exact TyPointers.ptrs_le f h hp hq

end Fir
