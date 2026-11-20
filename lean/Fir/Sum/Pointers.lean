import Fir.Sum.Dialect
import Fir.Execution.Observe

/-!
# The pointers of a sum's values

A value of a summed type holds the pointers that it holds on its own side,
and replacing them acts on its own side, so the laws of each side give the
sum's. `Empty`, the own types of a dialect that has none, has no value, so
its values hold no pointer.
-/

namespace Fir

/-- `Empty` has no value, so no value of it holds a pointer. -/
instance instTyPointersEmpty : TyPointers Empty where
  ptrs {t} := nomatch t
  map _ {t} := nomatch t
  map_some {t} := nomatch t
  map_map _ _ {t} := nomatch t
  map_mono _ {t} := nomatch t
  map_le _ _ {t} := nomatch t
  ptrs_le _ {t} := nomatch t

/-- A value of a summed type holds the pointers it holds on its own side, and
replacing them acts on its own side. -/
instance instTyPointersSum {A B : Type} [TyDenote A] [TyDenote B] [TyRefinement A]
    [TyRefinement B] [TyPointers A] [TyPointers B] : TyPointers (A ⊕ B) where
  ptrs {t} := match t with
    | .inl t => TyPointers.ptrs (Ty := A) (t := t)
    | .inr t => TyPointers.ptrs (Ty := B) (t := t)
  map f {t} := match t with
    | .inl t => TyPointers.map (Ty := A) f (t := t)
    | .inr t => TyPointers.map (Ty := B) f (t := t)
  map_some {t} v := match t, v with
    | .inl _, v => TyPointers.map_some (Ty := A) v
    | .inr _, v => TyPointers.map_some (Ty := B) v
  map_map f g {t} v := match t, v with
    | .inl _, v => TyPointers.map_map (Ty := A) f g v
    | .inr _, v => TyPointers.map_map (Ty := B) f g v
  map_mono f {t} a b h := match t, a, b, h with
    | .inl _, _, _, h => TyPointers.map_mono (Ty := A) f h
    | .inr _, _, _, h => TyPointers.map_mono (Ty := B) f h
  map_le f g {t} v h := match t, v, h with
    | .inl _, v, h => TyPointers.map_le (Ty := A) f g v h
    | .inr _, v, h => TyPointers.map_le (Ty := B) f g v h
  ptrs_le f {t} a b _ _ _ h hp hq := match t, a, b, h, hp with
    | .inl _, _, _, h, hp => TyPointers.ptrs_le (Ty := A) f h hp hq
    | .inr _, _, _, h, hp => TyPointers.ptrs_le (Ty := B) f h hp hq

/-- The types of a sum hold pointers as summed types do. -/
instance instTyPointersSumTy {base e : Dialect} [TyDenote base.Ty] [TyDenote e.Ty]
    [TyRefinement base.Ty] [TyRefinement e.Ty] [TyPointers base.Ty] [TyPointers e.Ty] :
    TyPointers (base ⊞ e).Ty :=
  instTyPointersSum

end Fir
