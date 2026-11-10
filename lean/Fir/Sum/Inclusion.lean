import Fir.Sum.Dialect

/-!
An extension is written over the dialects it depends on: its classes are
stated for `dep.over e`, whose types are `dep`'s and its own. A module may
hold more dialects than `e` depends on, so `e` must also work over a larger
base `big` that holds `dep` (ADR-2026-11-10-1310). What `e` needs of `big`
is an _inclusion_ of `dep`'s types in `big`'s: each type of `dep` is a type
of `big`, `big` can say which of its types are `dep`'s, and a value of a
type of `dep` is a value of that type in `big`, and back.

The base of a sum is held by the sum through `.inl`. Inclusions compose, and
an inclusion of the base's types gives one of the types of an extension over
it. So a dialect held anywhere in a nested sum, such as the core in
`core ⊞ a ⊞ b`, is included in the sum's types.

Values cross an inclusion one way and back. An inclusion is _lawful_ when
crossing it keeps which values are poison and which values refine others.
Each inclusion built here is lawful when its parts are.

This section gives, in order: an inclusion and its three constructions, how
a vector of values and a list of types cross one, and lawful inclusions.
-/

namespace Fir

/-!
# Inclusions of types
-/

/-- An inclusion of the types `A` in the types `B`: a type of `A` as a type
of `B`, the type of `A` that a type of `B` is, if any, and the values of a
type of `A` as the values of its type in `B`, and back. Each map undoes the
other. -/
structure TyIncl (A B : Type) [TyDenote A] [TyDenote B] where
  incl : A → B
  proj : B → Option A
  up : {a : A} → ⟦a⟧ → ⟦incl a⟧
  down : {a : A} → ⟦incl a⟧ → ⟦a⟧
  proj_incl : ∀ a, proj (incl a) = some a
  incl_proj : ∀ {b : B} {a : A}, proj b = some a → incl a = b
  down_up : ∀ {a : A} (x : ⟦a⟧), down (up x) = x
  up_down : ∀ {a : A} (x : ⟦incl a⟧), up (down x) = x

namespace TyIncl

variable {A B C : Type} [TyDenote A] [TyDenote B] [TyDenote C]

/-- The types `A` are the left side of `A ⊕ B`, as the base's types are in
a sum. A value does not change. -/
def inl : TyIncl A (A ⊕ B) where
  incl := .inl
  proj := Sum.getLeft?
  up x := x
  down x := x
  proj_incl _ := rfl
  incl_proj {b _} h := by cases b <;> simp_all
  down_up _ := rfl
  up_down _ := rfl

/-- An inclusion of `A` in `B` includes `A ⊕ C` in `B ⊕ C`, and keeps each
type of `C`: the types of an extension over a base, as types of the same
extension over a larger base. -/
def over (ι : TyIncl A B) : TyIncl (A ⊕ C) (B ⊕ C) where
  incl
    | .inl a => .inl (ι.incl a)
    | .inr c => .inr c
  proj
    | .inl b => (ι.proj b).map .inl
    | .inr c => some (.inr c)
  up {t} x := match t, x with
    | .inl _, x => ι.up x
    | .inr _, x => x
  down {t} x := match t, x with
    | .inl _, x => ι.down x
    | .inr _, x => x
  proj_incl
    | .inl a => by simp [ι.proj_incl a]
    | .inr _ => rfl
  incl_proj {b t} h := by
    cases b with
    | inl b =>
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      exact congrArg Sum.inl (ι.incl_proj ha)
    | inr c => cases h; rfl
  down_up {t} x := match t, x with
    | .inl _, x => ι.down_up x
    | .inr _, _ => rfl
  up_down {t} x := match t, x with
    | .inl _, x => ι.up_down x
    | .inr _, _ => rfl

/-- An inclusion of `A` in `B` and one of `B` in `C` include `A` in `C`. -/
def comp (ι : TyIncl A B) (κ : TyIncl B C) : TyIncl A C where
  incl a := κ.incl (ι.incl a)
  proj c := (κ.proj c).bind ι.proj
  up x := κ.up (ι.up x)
  down x := ι.down (κ.down x)
  proj_incl a := by simp [κ.proj_incl, ι.proj_incl]
  incl_proj h := by
    obtain ⟨b, hb, ha⟩ := Option.bind_eq_some_iff.mp h
    rw [ι.incl_proj ha, κ.incl_proj hb]
  down_up x := by
    show ι.down (κ.down (κ.up (ι.up x))) = x
    rw [κ.down_up, ι.down_up]
  up_down x := by
    show κ.up (ι.up (ι.down (κ.down x))) = x
    rw [ι.up_down, κ.up_down]

end TyIncl

/-!
# Crossing an inclusion
-/

section
variable {A B : Type} [TyDenote A] [TyDenote B]

/-- A vector of values of the types `A`, as values of their types in `B`. -/
def HVector.up (ι : TyIncl A B) : {ts : List A} → HVector toType ts →
    HVector toType (ts.map ι.incl)
  | [], .nil => .nil
  | _ :: _, .cons x xs => .cons (ι.up x) (HVector.up ι xs)

/-- A vector of values of the types `A` seen in `B`, as values of the types
`A`. -/
def HVector.down (ι : TyIncl A B) : {ts : List A} → HVector toType (ts.map ι.incl) →
    HVector toType ts
  | [], .nil => .nil
  | _ :: _, .cons x xs => .cons (ι.down x) (HVector.down ι xs)

/-- Crossing up and back gives a vector back. -/
theorem HVector.down_up (ι : TyIncl A B) : ∀ {ts : List A} (xs : HVector toType ts),
    HVector.down ι (HVector.up ι xs) = xs
  | [], .nil => rfl
  | _ :: _, .cons x xs => by simp [HVector.up, HVector.down, ι.down_up, HVector.down_up ι xs]

/-- Crossing back and up gives a vector back. -/
theorem HVector.up_down (ι : TyIncl A B) : ∀ {ts : List A}
    (xs : HVector toType (ts.map ι.incl)), HVector.up ι (HVector.down ι xs) = xs
  | [], .nil => rfl
  | _ :: _, .cons x xs => by simp [HVector.up, HVector.down, ι.up_down, HVector.up_down ι xs]

/-- Projecting a list of included types gives the list back. -/
theorem TyIncl.mapM_proj_map (ι : TyIncl A B) (ts : List A) :
    (ts.map ι.incl).mapM ι.proj = some ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [List.mapM_cons, ι.proj_incl, ih]

/-- A list of types that projects is the inclusion of its projection. -/
theorem TyIncl.eq_map_of_mapM_proj (ι : TyIncl A B) {ts : List B} {ts' : List A}
    (h : ts.mapM ι.proj = some ts') : ts = ts'.map ι.incl := by
  induction ts generalizing ts' with
  | nil => simp at h; simp [h]
  | cons t ts ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, rest, hr, rfl⟩ := h
    simp [ι.incl_proj ha, ih hr]

end

/-!
# Lawful inclusions
-/

/-- An inclusion is lawful when crossing it keeps which values are poison
and which values refine others. -/
structure TyIncl.Lawful {A B : Type} [TyDenote A] [TyDenote B] [TyPoison A] [TyPoison B]
    [TyRefinement A] [TyRefinement B] (ι : TyIncl A B) : Prop where
  isPoison_up : ∀ {a : A} (x : ⟦a⟧), TyPoison.IsPoison (ι.up x) ↔ TyPoison.IsPoison x
  isRefinedBy_up : ∀ {a : A} (x y : ⟦a⟧),
    TyRefinement.IsRefinedBy (ι.up x) (ι.up y) ↔ TyRefinement.IsRefinedBy x y

namespace TyIncl

variable {A B C : Type} [TyDenote A] [TyDenote B] [TyDenote C] [TyPoison A] [TyPoison B]
  [TyPoison C] [TyRefinement A] [TyRefinement B] [TyRefinement C]

/-- The left side of a sum is a lawful inclusion. -/
theorem lawful_inl : (inl : TyIncl A (A ⊕ B)).Lawful :=
  ⟨fun _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-- An inclusion over a lawful one is lawful. -/
theorem Lawful.over {ι : TyIncl A B} (h : ι.Lawful) : (ι.over (C := C)).Lawful where
  isPoison_up {t} x := match t, x with
    | .inl _, x => h.isPoison_up x
    | .inr _, _ => Iff.rfl
  isRefinedBy_up {t} x y := match t, x, y with
    | .inl _, x, y => h.isRefinedBy_up x y
    | .inr _, _, _ => Iff.rfl

/-- Two lawful inclusions compose to a lawful one. -/
theorem Lawful.comp {ι : TyIncl A B} {κ : TyIncl B C} (hι : ι.Lawful) (hκ : κ.Lawful) :
    (ι.comp κ).Lawful where
  isPoison_up x := (hκ.isPoison_up (ι.up x)).trans (hι.isPoison_up x)
  isRefinedBy_up x y := (hκ.isRefinedBy_up (ι.up x) (ι.up y)).trans (hι.isRefinedBy_up x y)

end TyIncl

end Fir
