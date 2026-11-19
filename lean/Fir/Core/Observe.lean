import Fir.Core.Values
import Fir.Execution.Observe

/-!
# The pointers of the core's values

A core value holds a pointer when its type is a pointer type `ptr<N>` and it
is not poison: the pointer of the memory numbered `N`. A value of an integer
or float type holds none. Replacing the pointer of a value of a pointer
type gives the pointer it is replaced by, or poison; the values of other
types stay as they are.
-/

namespace Fir

open Memory

/-- The pointer a value of `ptr<n>` holds, with its memory's number, if it is
not poison. -/
def PoisonOr.ptrsOf (n : Nat) : PoisonOr Pointer → List (Nat × Pointer)
  | .value p => [(n, p)]
  | .poison => []

/-- A value of `ptr<n>` with its pointer replaced, or poison. -/
def PoisonOr.mapPtr (f : Nat → Pointer → Option Pointer) (n : Nat) :
    PoisonOr Pointer → PoisonOr Pointer
  | .value p => match f n p with
    | some q => .value q
    | none => .poison
  | .poison => .poison

/-- The pointers a core value holds. -/
def Core.Ty.ptrs : {t : Core.Ty} → ⟦t⟧ → List (Nat × Pointer)
  | .ptr n, v => PoisonOr.ptrsOf n v
  | .int _, _ | .float _ _, _ => []

/-- A core value with its pointer replaced. -/
def Core.Ty.mapPtrs (f : Nat → Pointer → Option Pointer) : {t : Core.Ty} → ⟦t⟧ → ⟦t⟧
  | .ptr n, v => PoisonOr.mapPtr f n v
  | .int _, v | .float _ _, v => v

/-- A value of a pointer type holds its pointer, and replacing it acts on
that pointer alone. -/
instance Core.instTyPointers : TyPointers Core.Ty where
  ptrs := Core.Ty.ptrs
  map := Core.Ty.mapPtrs
  map_some {t} v := by
    cases t with
    | ptr _ => cases v <;> rfl
    | _ => rfl
  map_map f g {t} v := by
    cases t with
    | ptr n =>
      cases v with
      | poison => rfl
      | value p => cases h : f n p <;> simp [Core.Ty.mapPtrs, PoisonOr.mapPtr, h] <;> rfl
    | _ => rfl
  map_mono f {t} a b h := by
    cases t with
    | ptr n =>
      cases a with
      | poison => exact trivial
      | value p =>
        cases b with
        | poison => exact (h : False).elim
        | value q =>
          cases (h : p = q)
          exact PoisonOr.isRefinedBy_refl (PoisonOr.mapPtr f n (.value p))
    | int _ => exact h
    | float _ _ => exact h
  map_le f g {t} v h := by
    cases t with
    | ptr n =>
      cases v with
      | poison => exact trivial
      | value p =>
        rcases h n p (List.mem_singleton_self _) with hf | hf
        · show PoisonOr.IsRefinedBy (PoisonOr.mapPtr f n (.value p)) _
          simp only [PoisonOr.mapPtr, hf]
          exact trivial
        · show PoisonOr.IsRefinedBy (PoisonOr.mapPtr f n (.value p))
            (PoisonOr.mapPtr g n (.value p))
          rw [PoisonOr.mapPtr, PoisonOr.mapPtr, hf]
          exact PoisonOr.isRefinedBy_refl _
    | int _ => exact PoisonOr.isRefinedBy_refl (α := BitVec _) v
    | float _ _ => exact PoisonOr.isRefinedBy_refl (α := BitVec _) v
  ptrs_le f {t} a b n p q h hp hq := by
    cases t with
    | ptr m =>
      cases a with
      | poison => cases hp
      | value p' =>
        simp only [Core.Ty.ptrs, PoisonOr.ptrsOf, List.mem_singleton, Prod.mk.injEq] at hp
        obtain ⟨hn, hp⟩ := hp
        subst hn hp
        have h' : PoisonOr.IsRefinedBy (PoisonOr.mapPtr f n (.value p)) b := h
        rw [PoisonOr.mapPtr, hq] at h'
        cases b with
        | poison => exact h'.elim
        | value r =>
          cases (h' : q = r)
          exact List.mem_singleton_self _
    | int _ | float _ _ => cases hp

/-- The core dialect's typed values hold pointers through the general
instance, named here because instance search does not find it for
`CoreDialect`. -/
instance Core.instHasPtrs : HasPtrs (DVal CoreDialect) := instHasPtrsDVal

end Fir
