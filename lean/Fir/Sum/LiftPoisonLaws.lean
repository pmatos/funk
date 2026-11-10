import Fir.Sum.Lift
import Fir.Sum.PoisonLaws

/-!
# The lift of a lawful extension is lawful

The lift of an extension that meets the poison obligations over `dep`
meets them over `big` (`Dialect.lift.lawfulPoison`), when the inclusion is
lawful and `e` accepts each type of `dep` whose inclusion `big` accepts.
Each op of the lift runs by `e`'s rule on the same values, which only
cross the inclusion, and a lawful inclusion keeps which values are poison
and which refine others. The lift accepts `big`'s types as `big` does, so
the sum `big ⊞ e.lift dep ι` is lawful by the theorem on sums
(`Dialect.lift.sum_lawfulPoison`).

The proof first shows that crossing a lawful inclusion keeps what the
obligations look at, as the section on a sum's poison obligations does for
the base's values in the sum.
-/

namespace Fir

/-!
# Values across a lawful inclusion
-/

section
variable {A B : Type} [TyDenote A] [TyDenote B] {ι : TyIncl A B}

/-- Two vectors cross up related by `r'` exactly when they are related by
`r`, when crossing one value up keeps the relation. -/
theorem HVector.forall₂_up {r : {a : A} → ⟦a⟧ → ⟦a⟧ → Prop} {r' : {b : B} → ⟦b⟧ → ⟦b⟧ → Prop}
    (hr : ∀ {a : A} (x y : ⟦a⟧), r' (ι.up x) (ι.up y) ↔ r x y) :
    ∀ {ts : List A} (xs ys : HVector toType ts),
      (HVector.up ι xs).Forall₂ r' (HVector.up ι ys) ↔ xs.Forall₂ r ys
  | [], .nil, .nil => Iff.rfl
  | _ :: _, .cons x xs, .cons y ys => and_congr (hr x y) (HVector.forall₂_up hr xs ys)

/-- Two vectors cross down related by `r` exactly when they are related by
`r'`, when crossing one value up keeps the relation. -/
theorem HVector.forall₂_down {r : {a : A} → ⟦a⟧ → ⟦a⟧ → Prop}
    {r' : {b : B} → ⟦b⟧ → ⟦b⟧ → Prop}
    (hr : ∀ {a : A} (x y : ⟦a⟧), r' (ι.up x) (ι.up y) ↔ r x y) {ts : List A}
    (xs ys : HVector toType (ts.map ι.incl)) :
    (HVector.down ι xs).Forall₂ r (HVector.down ι ys) ↔ xs.Forall₂ r' ys := by
  rw [← HVector.forall₂_up hr, HVector.up_down, HVector.up_down]

/-- What a computation over the types `A` may end with, moved up to `B`. -/
theorem HVector.map_up {ts : List A} (s : SetM (HVector toType ts)) (x) :
    (HVector.up ι <$> s) x ↔
      (∃ a, s (.ok a) ∧ x = .ok (HVector.up ι a)) ∨ ∃ r, s (.ub r) ∧ x = .ub r :=
  Iff.rfl

variable [TyPoison A] [TyPoison B] [TyRefinement A] [TyRefinement B]

/-- A value crossed down is poison exactly when it was. -/
theorem TyIncl.Lawful.isPoison_down (h : ι.Lawful) {a : A} (x : ⟦ι.incl a⟧) :
    TyPoison.IsPoison (ι.down x) ↔ TyPoison.IsPoison x := by
  rw [← h.isPoison_up, ι.up_down]

/-- A vector crossed down holds poison exactly when it did. -/
theorem HVector.any_down (h : ι.Lawful) : ∀ {ts : List A} (xs : HVector toType (ts.map ι.incl)),
    (HVector.down ι xs).Any TyPoison.IsPoison ↔ xs.Any TyPoison.IsPoison
  | [], .nil => Iff.rfl
  | _ :: _, .cons x xs => or_congr (h.isPoison_down x) (HVector.any_down h xs)

/-- A vector crossed up is all poison exactly when it was. -/
theorem HVector.all_up (h : ι.Lawful) : ∀ {ts : List A} (xs : HVector toType ts),
    (HVector.up ι xs).All TyPoison.IsPoison ↔ xs.All TyPoison.IsPoison
  | [], .nil => Iff.rfl
  | _ :: _, .cons x xs => and_congr (h.isPoison_up x) (HVector.all_up h xs)

/-- A value crossed up is poison or equal to another crossed up exactly
when it was. -/
theorem TyIncl.Lawful.poisonOrEq_up (h : ι.Lawful) {a : A} (x y : ⟦a⟧) :
    (TyPoison.IsPoison (ι.up x) ∨ ι.up x = ι.up y) ↔ (TyPoison.IsPoison x ∨ x = y) :=
  or_congr (h.isPoison_up x)
    ⟨fun hxy => by rw [← ι.down_up x, hxy, ι.down_up], congrArg _⟩

/-- Refinement of what a computation over `A` may end with carries over to
`B`. -/
theorem HVector.isRefinedBy_map_up (h : ι.Lawful) {ts : List A} {s t : SetM (HVector toType ts)}
    (hst : SetM.IsRefinedBy (HVector.Forall₂ TyRefinement.IsRefinedBy) s t) :
    SetM.IsRefinedBy (HVector.Forall₂ TyRefinement.IsRefinedBy)
      (HVector.up ι <$> s) (HVector.up ι <$> t) := by
  intro x hx
  rcases (HVector.map_up t x).1 hx with ⟨b, hb, rfl⟩ | ⟨r, hr, rfl⟩
  · obtain ⟨y, hy, hyb⟩ := hst _ hb
    cases y with
    | ok a =>
      exact ⟨.ok (HVector.up ι a), (HVector.map_up s _).2 (.inl ⟨a, hy, rfl⟩),
        (HVector.forall₂_up h.isRefinedBy_up a b).2 hyb⟩
    | ub r => exact ⟨.ub r, (HVector.map_up s _).2 (.inr ⟨r, hy, rfl⟩), trivial⟩
  · obtain ⟨y, hy, hyb⟩ := hst _ hr
    cases y with
    | ok a => exact absurd hyb id
    | ub r' => exact ⟨.ub r', (HVector.map_up s _).2 (.inr ⟨r', hy, rfl⟩), trivial⟩

end

/-!
# The lift's obligations
-/

namespace Dialect.lift

variable {e dep big : Dialect} [TyDenote dep.Ty] [TyDenote big.Ty] [TyDenote e.Ty]
  {ι : TyIncl dep.Ty big.Ty} [TyPoison dep.Ty] [TyPoison big.Ty] [TyPoison e.Ty]
  [TyRefinement dep.Ty] [TyRefinement big.Ty] [TyRefinement e.Ty]

variable (e) in
/-- The inclusion of the lift's types is lawful when `ι` is. -/
theorem incl_lawful (h : ι.Lawful) : (incl e ι).Lawful := h.over

/-- A vector of `e`'s operand types is filled by another exactly when it
is across the inclusion. -/
theorem isFilledBy_down (h : ι.Lawful) {ts : List (dep.over e).Ty}
    (xs ys : HVector toType (ts.map (incl e ι).incl)) :
    (HVector.down (incl e ι) xs).IsFilledBy (d := dep.over e) (HVector.down (incl e ι) ys) ↔
      xs.IsFilledBy (d := big.over (e.lift dep ι)) ys := by
  unfold HVector.IsFilledBy
  rw [HVector.any_down (incl_lawful e h)]
  exact and_congr Iff.rfl (HVector.forall₂_down (incl_lawful e h).poisonOrEq_up xs ys)

variable [DialectSignature (dep.over e)] [DialectValidation big] [DialectValidation (dep.over e)]

omit [TyPoison dep.Ty] [TyPoison big.Ty] [TyPoison e.Ty] [TyRefinement dep.Ty] [TyRefinement big.Ty]
  [TyRefinement e.Ty] in
/-- An op of the lift whose instance the lift accepts is one that `e`
accepts, when `e` accepts each type of `dep` whose inclusion `big`
accepts. -/
theorem typesValid_lift (hty : ∀ t : dep.Ty, validTy (ι.incl t) → validTy (d := dep.over e) (.inl t))
    {o : e.Op} (hv : TypesValid (d := big.over (e.lift dep ι)) o) :
    TypesValid (d := dep.over e) o := by
  have h : ∀ t : (dep.over e).Ty, validTy (d := big.over (e.lift dep ι)) ((incl e ι).incl t) →
      validTy (d := dep.over e) t
    | .inl t, h => hty t h
    | .inr _, h => h
  exact ⟨fun t ht => h t (hv.1 _ (List.mem_map_of_mem ht)),
    fun t ht => h t (hv.2 _ (List.mem_map_of_mem ht))⟩

variable [DialectDenote (dep.over e) SetM]

omit [DialectValidation big] [DialectValidation (dep.over e)] in
/-- An op of `e` that propagates poison over `dep` propagates it in the
lift. -/
theorem propagates_lift (h : ι.Lawful) {o : e.Op} (hp : PropagatesPoison (d := dep.over e) o) :
    PropagatesPoison (d := big.over (e.lift dep ι)) o where
  poisonOut args hany rs hden := by
    rcases (HVector.map_up _ _).1 hden with ⟨a, ha, he⟩ | ⟨r, -, he⟩
    · cases he
      exact (HVector.all_up (incl_lawful e h) a).2
        (hp.poisonOut _ ((HVector.any_down (incl_lawful e h) args).2 hany) a ha)
    · cases he
  ubByOwnRules args r hany hden := by
    rcases (HVector.map_up _ _).1 hden with ⟨a, -, he⟩ | ⟨r', hr, he⟩
    · cases he
    · cases he
      obtain ⟨args', hfill, r'', hub⟩ :=
        hp.ubByOwnRules _ r ((HVector.any_down (incl_lawful e h) args).2 hany) hr
      refine ⟨HVector.up (incl e ι) args', ?_, r'',
        (HVector.map_up _ _).2 (.inr ⟨r'', ?_, rfl⟩)⟩
      · rw [← isFilledBy_down h, HVector.down_up]
        exact hfill
      · show DialectDenote.denote (m := SetM) (d := dep.over e) o
          (HVector.down (incl e ι) (HVector.up (incl e ι) args')) _
        rw [HVector.down_up]
        exact hub

variable [DialectEffects (dep.over e)] [DialectCall (dep.over e)]
  [DialectSignature big] [DialectDenote big SetM] [DialectEffects big] [DialectCall big]

/-- The lift of a lawful extension is lawful over a lawful `big`, when the
inclusion is lawful and `e` accepts each type of `dep` whose inclusion `big`
accepts. -/
theorem lawfulPoison [h₁ : LawfulDialectPoison big] [h₂ : LawfulDialectPoison (dep.over e)]
    (hι : ι.Lawful)
    (hty : ∀ t : dep.Ty, validTy (ι.incl t) → validTy (d := dep.over e) (.inl t)) :
    LawfulDialectPoison (big.over (e.lift dep ι)) where
  poison_isRefinedBy {t} := match t with
    | .inl _ => fun hv p v hp => h₁.poison_isRefinedBy hv p v hp
    | .inr t => fun hv p v hp => h₂.poison_isRefinedBy (t := .inr t) hv p v hp
  propagates o hv hc := propagates_lift hι (h₂.propagates o (typesValid_lift hty hv) hc)
  returnsOnDefined o hv hc := by
    obtain ⟨args, hnp, rs, hrs⟩ := h₂.returnsOnDefined o (typesValid_lift hty hv) hc
    refine ⟨HVector.up (incl e ι) args, ?_, HVector.up (incl e ι) rs,
      (HVector.map_up _ _).2 (.inl ⟨rs, ?_, rfl⟩)⟩
    · rw [← HVector.any_down (incl_lawful e hι), HVector.down_up]
      exact hnp
    · show DialectDenote.denote (m := SetM) (d := dep.over e) o
        (HVector.down (incl e ι) (HVector.up (incl e ι) args)) _
      rw [HVector.down_up]
      exact hrs
  total o hv hr args := by
    have ht := h₂.total o (typesValid_lift hty hv) hr (HVector.down (incl e ι) args)
    refine ⟨fun hn => ?_, fun hn => ht.2 hn⟩
    obtain ⟨x, hx⟩ := ht.1 hn
    cases x with
    | ok a => exact ⟨_, (HVector.map_up _ _).2 (.inl ⟨a, hx, rfl⟩)⟩
    | ub r => exact ⟨_, (HVector.map_up _ _).2 (.inr ⟨r, hx, rfl⟩)⟩
  monotone o hv hr args args' hargs := by
    have hm := h₂.monotone o (typesValid_lift hty hv) hr (HVector.down (incl e ι) args)
      (HVector.down (incl e ι) args')
      ((HVector.forall₂_down (incl_lawful e hι).isRefinedBy_up args args').2 hargs)
    exact ⟨fun hn => HVector.isRefinedBy_map_up (incl_lawful e hι) (hm.1 hn), hm.2⟩

/-- The sum of a lawful `big` and the lift of a lawful extension into it is
lawful, when the inclusion is lawful and `e` accepts each type of `dep`
whose inclusion `big` accepts. -/
theorem sum_lawfulPoison [LawfulDialectPoison big] [LawfulDialectPoison (dep.over e)]
    (hι : ι.Lawful)
    (hty : ∀ t : dep.Ty, validTy (ι.incl t) → validTy (d := dep.over e) (.inl t)) :
    LawfulDialectPoison (big ⊞ e.lift dep ι) :=
  have := lawfulPoison (e := e) hι hty
  Dialect.sum.lawfulPoison fun _ h => h

end Dialect.lift

end Fir
