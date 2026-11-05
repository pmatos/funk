import Init

/-!
How `Except` computes on a value or an error, as `simp` lemmas, for the
proofs that `fir-ref`'s lexer and readers compute what the spec's compute.
-/

namespace FirRef

@[simp] theorem okBind {ε α β : Type} (a : α) (k : α → Except ε β) :
    (Except.ok a >>= k) = k a := rfl

@[simp] theorem errorBind {ε α β : Type} (e : ε) (k : α → Except ε β) :
    (Except.error e >>= k) = Except.error e := rfl

@[simp] theorem okMap {ε α β : Type} (f : α → β) (a : α) :
    (f <$> (Except.ok a : Except ε α)) = .ok (f a) := rfl

@[simp] theorem errorMap {ε α β : Type} (f : α → β) (e : ε) :
    (f <$> (Except.error e : Except ε α)) = .error e := rfl

@[simp] theorem okExceptMap {ε α β : Type} (f : α → β) (a : α) :
    (Except.ok a : Except ε α).map f = .ok (f a) := rfl

@[simp] theorem errorExceptMap {ε α β : Type} (f : α → β) (e : ε) :
    (Except.error e : Except ε α).map f = .error e := rfl

/-- Two computations whose results agree under `f` and `g` both fail with
the same error, or both succeed with results that `f` and `g` map alike. -/
theorem map_agree {ε α β γ : Type} {x : Except ε α} {y : Except ε β} {f : α → γ} {g : β → γ}
    (h : x.map f = y.map g) :
    (∃ e, x = .error e ∧ y = .error e) ∨ (∃ a b, x = .ok a ∧ y = .ok b ∧ f a = g b) := by
  rcases x with e | a <;> rcases y with e' | b <;>
    simp only [okExceptMap, errorExceptMap, Except.ok.injEq, Except.error.injEq,
      reduceCtorEq] at h
  · exact .inl ⟨e, rfl, by rw [h]⟩
  · exact .inr ⟨a, b, rfl, rfl, h⟩

end FirRef
