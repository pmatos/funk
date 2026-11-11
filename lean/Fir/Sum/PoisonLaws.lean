import Fir.Sum.Dialect

/-!
# The sum of lawful dialects is lawful

A sum meets the poison obligations when its two sides do
(`Dialect.sum.lawfulPoison`). Each op of the sum meets them as an op of its
own side: an op of the base runs by the base's rule on the same values,
which only change the type they are seen at, and an op of `e` runs by
`e`'s rule over the base. The one condition is that `e` accepts every type
that the base accepts, since `e`'s obligations cover only the instances
whose types `e` accepts, and the sum accepts the base's types as the base
says.

The proof first shows that moving a vector of values between the base's
types and the sum's keeps what the obligations look at: which values are
poison, which vectors fill the poison of others, and which refine others.
-/

namespace Fir

/-!
# Values moved between the base and the sum
-/

section
variable {base e : Dialect} [TyDenote base.Ty] [TyDenote e.Ty]

/-- Moving a vector to the sum's types and back gives it back. -/
theorem HVector.ofSum_toSum : ∀ {ts : List base.Ty} (xs : HVector toType ts),
    HVector.ofSum (e := e) (HVector.toSum xs) = xs
  | [], .nil => rfl
  | _ :: _, .cons x xs => by simp [HVector.toSum, HVector.ofSum, HVector.ofSum_toSum xs]

/-- Moving a vector to the base's types and back gives it back. -/
theorem HVector.toSum_ofSum : ∀ {ts : List base.Ty}
    (xs : HVector (toType (Ty := (base ⊞ e).Ty)) (ts.map .inl)),
    HVector.toSum (HVector.ofSum xs) = xs
  | [], .nil => rfl
  | _ :: _, .cons x xs => by simp [HVector.toSum, HVector.ofSum, HVector.toSum_ofSum xs]

/-- Two vectors of the sum's types `.inl t` are related position by position
by a relation of the sum's values exactly when they are at the base's
types by the same relation. -/
theorem HVector.forall₂_ofSum {r : {t : base.Ty} → ⟦t⟧ → ⟦t⟧ → Prop}
    {r' : {t : (base ⊞ e).Ty} → ⟦t⟧ → ⟦t⟧ → Prop} (hr : ∀ {t : base.Ty} (x y : ⟦t⟧),
      r' (t := .inl t) x y ↔ r x y) :
    ∀ {ts : List base.Ty} (xs ys : HVector (toType (Ty := (base ⊞ e).Ty)) (ts.map .inl)),
    (HVector.ofSum xs).Forall₂ r (HVector.ofSum ys) ↔ xs.Forall₂ r' ys
  | [], .nil, .nil => Iff.rfl
  | _ :: _, .cons x xs, .cons y ys => and_congr (hr x y).symm (HVector.forall₂_ofSum hr xs ys)

variable [TyPoison base.Ty] [TyPoison e.Ty]

/-- A vector holds poison at the base's types exactly when it does at the
sum's. -/
theorem HVector.any_ofSum : ∀ {ts : List base.Ty}
    (xs : HVector (toType (Ty := (base ⊞ e).Ty)) (ts.map .inl)),
    (HVector.ofSum xs).Any TyPoison.IsPoison ↔ xs.Any TyPoison.IsPoison
  | [], .nil => Iff.rfl
  | _ :: _, .cons _ xs => or_congr Iff.rfl (HVector.any_ofSum xs)

/-- A vector is all poison at the sum's types exactly when it is at the
base's. -/
theorem HVector.all_toSum : ∀ {ts : List base.Ty} (xs : HVector toType ts),
    (HVector.toSum (e := e) xs).All TyPoison.IsPoison ↔ xs.All TyPoison.IsPoison
  | [], .nil => Iff.rfl
  | _ :: _, .cons _ xs => and_congr Iff.rfl (HVector.all_toSum xs)

end

namespace Dialect.sum

variable {base e : Dialect}

section
variable [DialectSignature base] [DialectSignature (base.over e)]
  [DialectValidation base] [DialectValidation (base.over e)]

/-- An op of the base whose instance the sum accepts is one that the base
accepts. -/
theorem typesValid_inl {o : base.Op} (hv : TypesValid (d := base ⊞ e) (.inl o)) :
    TypesValid o :=
  ⟨fun t ht => hv.1 (.inl t) (List.mem_map_of_mem ht),
    fun t ht => hv.2 (.inl t) (List.mem_map_of_mem ht)⟩

/-- An op of `e` whose instance the sum accepts is one that `e` accepts,
when `e` accepts every type that the base accepts. -/
theorem typesValid_inr (hty : ∀ t : base.Ty, validTy t → validTy (d := base.over e) (.inl t))
    {o : e.Op} (hv : TypesValid (d := base ⊞ e) (.inr o)) : TypesValid (d := base.over e) o := by
  have h : ∀ t : base.Ty ⊕ e.Ty, validTy (d := base ⊞ e) t → validTy (d := base.over e) t
    | .inl t, h => hty t h
    | .inr _, h => h
  exact ⟨fun t ht => h t (hv.1 t ht), fun t ht => h t (hv.2 t ht)⟩

end

variable [TyDenote base.Ty] [TyDenote e.Ty]

/-- What a computation of the base may end with, moved to the sum's types. -/
theorem map_toSum {ts : List base.Ty} (s : SetM (HVector toType ts)) (x) :
    (HVector.toSum (e := e) <$> s) x ↔
      (∃ a, s (.ok a) ∧ x = .ok (HVector.toSum a)) ∨ ∃ r, s (.ub r) ∧ x = .ub r :=
  Iff.rfl

variable [TyPoison base.Ty] [TyPoison e.Ty]

/-- A vector of the sum's types `.inl t` is filled by another exactly when
it is at the base's types. -/
theorem isFilledBy_ofSum {ts : List base.Ty}
    (xs ys : HVector (toType (Ty := (base ⊞ e).Ty)) (ts.map .inl)) :
    (HVector.ofSum xs).IsFilledBy (HVector.ofSum ys) ↔ xs.IsFilledBy (d := base ⊞ e) ys := by
  unfold HVector.IsFilledBy
  rw [HVector.any_ofSum]
  exact and_congr Iff.rfl (HVector.forall₂_ofSum
    (r := fun x y => TyPoison.IsPoison x ∨ x = y) (fun _ _ => Iff.rfl) xs ys)

variable [TyRefinement base.Ty] [TyRefinement e.Ty]

omit [TyPoison base.Ty] [TyPoison e.Ty] in
/-- Values of the sum's types refine themselves when each side's do. -/
theorem isRefinedBy_refl (hb : ∀ {t : base.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (he : ∀ {t : e.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v) :
    ∀ {t : (base ⊞ e).Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v
  | .inl _, v => hb v
  | .inr _, v => he v

omit [TyPoison base.Ty] [TyPoison e.Ty] in
/-- Values of the sum's types refine transitively when each side's do. -/
theorem isRefinedBy_trans
    (hb : ∀ {t : base.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (he : ∀ {t : e.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w) :
    ∀ {t : (base ⊞ e).Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w
  | .inl _, _, _, _, h₁, h₂ => hb h₁ h₂
  | .inr _, _, _, _, h₁, h₂ => he h₁ h₂

omit [TyPoison base.Ty] [TyPoison e.Ty] in
/-- Two vectors of the sum's types `.inl t` are related by the sum's
refinement exactly when they are by the base's. -/
theorem forall₂_refines_ofSum {ts : List base.Ty}
    (xs ys : HVector (toType (Ty := (base ⊞ e).Ty)) (ts.map .inl)) :
    (HVector.ofSum xs).Forall₂ TyRefinement.IsRefinedBy (HVector.ofSum ys) ↔
      xs.Forall₂ TyRefinement.IsRefinedBy ys :=
  HVector.forall₂_ofSum (r := TyRefinement.IsRefinedBy) (fun _ _ => Iff.rfl) xs ys

omit [TyPoison base.Ty] [TyPoison e.Ty] in
/-- Refinement of what a computation of the base may end with carries over to
the sum's types. -/
theorem isRefinedBy_map_toSum {ts : List base.Ty} {s t : SetM (HVector toType ts)}
    (h : SetM.IsRefinedBy (HVector.Forall₂ TyRefinement.IsRefinedBy) s t) :
    SetM.IsRefinedBy (HVector.Forall₂ TyRefinement.IsRefinedBy)
      (HVector.toSum (e := e) <$> s) (HVector.toSum <$> t) := by
  intro x hx
  rcases (map_toSum t x).1 hx with ⟨b, hb, rfl⟩ | ⟨r, hr, rfl⟩
  · obtain ⟨y, hy, hyb⟩ := h _ hb
    cases y with
    | ok a =>
      refine ⟨.ok (HVector.toSum a), (map_toSum s _).2 (.inl ⟨a, hy, rfl⟩), ?_⟩
      show HVector.Forall₂ _ _ _
      rw [← forall₂_refines_ofSum, HVector.ofSum_toSum, HVector.ofSum_toSum]
      exact hyb
    | ub r => exact ⟨.ub r, (map_toSum s _).2 (.inr ⟨r, hy, rfl⟩), trivial⟩
  · obtain ⟨y, hy, hyb⟩ := h _ hr
    cases y with
    | ok a => exact absurd hyb id
    | ub r' => exact ⟨.ub r', (map_toSum s _).2 (.inr ⟨r', hy, rfl⟩), trivial⟩

variable [DialectSignature base] [DialectSignature (base.over e)]
  [DialectDenote base SetM] [DialectDenote (base.over e) SetM]

omit [TyRefinement base.Ty] [TyRefinement e.Ty] in
/-- An op of the base that propagates poison in the base propagates it in
the sum. -/
theorem propagates_inl {o : base.Op} (h : PropagatesPoison o) :
    PropagatesPoison (d := base ⊞ e) (.inl o) where
  poisonOut args hany rs hden := by
    rcases (map_toSum _ _).1 hden with ⟨a, ha, he⟩ | ⟨r, -, he⟩
    · cases he
      exact (HVector.all_toSum a).2 (h.poisonOut _ ((HVector.any_ofSum args).2 hany) a ha)
    · cases he
  ubByOwnRules args r hany hden := by
    rcases (map_toSum _ _).1 hden with ⟨a, -, he⟩ | ⟨r', hr, he⟩
    · cases he
    · cases he
      obtain ⟨args', hfill, r'', hub⟩ := h.ubByOwnRules _ r ((HVector.any_ofSum args).2 hany) hr
      refine ⟨HVector.toSum args', ?_, r'', (map_toSum _ _).2 (.inr ⟨r'', ?_, rfl⟩)⟩
      · rw [← isFilledBy_ofSum, HVector.ofSum_toSum]
        exact hfill
      · show DialectDenote.denote (m := SetM) o (HVector.ofSum (HVector.toSum args')) _
        rw [HVector.ofSum_toSum]
        exact hub

variable [DialectEffects base] [DialectEffects (base.over e)] [DialectMemOver base e]
  [DialectCall base] [DialectCall (base.over e)]
  [DialectValidation base] [DialectValidation (base.over e)]

/-- Two lawful dialects make a lawful sum, when `e` accepts every type that
the base accepts: each op meets the obligations as its own side's op. -/
theorem lawfulPoison [h₁ : LawfulDialectPoison base] [h₂ : LawfulDialectPoison (base.over e)]
    (hty : ∀ t : base.Ty, validTy t → validTy (d := base.over e) (.inl t)) :
    LawfulDialectPoison (base ⊞ e) where
  poison_isRefinedBy {t} := match t with
    | .inl _ => fun hv p v hp => h₁.poison_isRefinedBy hv p v hp
    | .inr t => fun hv p v hp => h₂.poison_isRefinedBy (t := .inr t) hv p v hp
  propagates
    | .inl o, hv, hc => propagates_inl (h₁.propagates o (typesValid_inl hv) hc)
    | .inr o, hv, hc =>
      have h := h₂.propagates o (typesValid_inr hty hv) hc
      ⟨h.1, h.2⟩
  returnsOnDefined
    | .inl o, hv, hc => by
      obtain ⟨args, hnp, rs, hrs⟩ := h₁.returnsOnDefined o (typesValid_inl hv) hc
      refine ⟨HVector.toSum args, ?_, HVector.toSum rs, (map_toSum _ _).2 (.inl ⟨rs, ?_, rfl⟩)⟩
      · rw [← HVector.any_ofSum, HVector.ofSum_toSum]
        exact hnp
      · show DialectDenote.denote (m := SetM) o (HVector.ofSum (HVector.toSum args)) _
        rw [HVector.ofSum_toSum]
        exact hrs
    | .inr o, hv, hc => h₂.returnsOnDefined o (typesValid_inr hty hv) hc
  total
    | .inl o, hv, hr => fun args => by
      have ht := h₁.total o (typesValid_inl hv) hr (HVector.ofSum args)
      refine ⟨fun hn => ?_, fun hn => ht.2 hn⟩
      obtain ⟨x, hx⟩ := ht.1 hn
      cases x with
      | ok a => exact ⟨_, (map_toSum _ _).2 (.inl ⟨a, hx, rfl⟩)⟩
      | ub r => exact ⟨_, (map_toSum _ _).2 (.inr ⟨r, hx, rfl⟩)⟩
    | .inr o, hv, hr => h₂.total o (typesValid_inr hty hv) hr
  monotone
    | .inl o, hv, hr => fun args args' hargs => by
      have hm := h₁.monotone o (typesValid_inl hv) hr (HVector.ofSum args) (HVector.ofSum args')
        ((forall₂_refines_ofSum args args').2 hargs)
      exact ⟨fun hn => isRefinedBy_map_toSum (hm.1 hn), hm.2⟩
    | .inr o, hv, hr => h₂.monotone o (typesValid_inr hty hv) hr

end Dialect.sum

end Fir
