/-!
# The interpreter's effects: choice and immediate UB

The interpreter is written once, against any monad with these two effects.
`Prog` is the free monad over them, so a run is a tree of choices, and each
`fir-ref` mode is a handler over that tree. The soundness of the modes is then
a property of the handlers alone, proved once, whatever the interpreter does.
-/

namespace FirOwn

/-- The effects of fir's core dialect: choose `w` arbitrary bits (`freeze`
of poison), and immediate UB with a reason. -/
class MonadFir (m : Type → Type) where
  choose : (w : Nat) → m (BitVec w)
  ub {α : Type} : String → m α

/-- The free monad over `MonadFir`: a tree whose inner nodes are choices. -/
inductive Prog (α : Type) where
  | pure (a : α)
  | choose (w : Nat) (k : BitVec w → Prog α)
  | ub (reason : String)

namespace Prog

def bind : Prog α → (α → Prog β) → Prog β
  | .pure a, f => f a
  | .choose w k, f => .choose w fun b => bind (k b) f
  | .ub r, _ => .ub r

instance : Monad Prog where
  pure := .pure
  bind := bind

instance : MonadFir Prog where
  choose w := .choose w .pure
  ub r := .ub r

theorem bind_pure (p : Prog α) : bind p .pure = p := by
  induction p with
  | pure a => rfl
  | choose w k ih => simp only [bind, ih]
  | ub r => rfl

theorem bind_assoc (p : Prog α) (f : α → Prog β) (g : β → Prog γ) :
    bind (bind p f) g = bind p (fun a => bind (f a) g) := by
  induction p with
  | pure a => rfl
  | choose w k ih => simp only [bind, ih]
  | ub r => rfl

instance : LawfulMonad Prog := LawfulMonad.mk' Prog
  (id_map := fun p => bind_pure p)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := bind_assoc)

/-- One outcome of a run: a result, or immediate UB. -/
inductive Ev (α : Type) where
  | ok (a : α)
  | ub (reason : String)
  deriving Repr, DecidableEq

/-- The semantics: the set of outcomes over all choices. This is the
definition that the spec and the proofs use. -/
def sem : Prog α → Ev α → Prop
  | .pure a, e => e = .ok a
  | .choose _ k, e => ∃ b, sem (k b) e
  | .ub r, e => e = .ub r

/-- Every bit-vector of width `w`. -/
def allBV (w : Nat) : List (BitVec w) :=
  (List.range (2 ^ w)).map (BitVec.ofNat w)

theorem mem_allBV (b : BitVec w) : b ∈ allBV w := by
  simp only [allBV, List.mem_map, List.mem_range]
  exact ⟨b.toNat, b.isLt, by simp⟩

/-- Exhaustive mode: every choice sequence whose total width fits in
`budget` bits. The flag is `true` when some branch exceeded the budget. -/
def exhaustive : Prog α → (budget : Nat) → List (Ev α) × Bool
  | .pure a, _ => ([.ok a], false)
  | .ub r, _ => ([.ub r], false)
  | .choose w k, n =>
    if w ≤ n then
      let rs := (allBV w).map fun b => exhaustive (k b) (n - w)
      (rs.flatMap (·.1), rs.any (·.2))
    else ([], true)

/-- Scripted mode: one natural number per choice. Returns the outcome and
whether any choice was used, or `none` if the script ran out. -/
def scripted : Prog α → List Nat → Option (Ev α × Bool)
  | .pure a, _ => some (.ok a, false)
  | .ub r, _ => some (.ub r, false)
  | .choose _ _, [] => none
  | .choose w k, c :: cs =>
    (scripted (k (BitVec.ofNat w c)) cs).map fun (e, _) => (e, true)

/-- Within its budget, exhaustive mode returns exactly the semantic set. -/
theorem exhaustive_eq_sem (p : Prog α) (n : Nat)
    (h : (exhaustive p n).2 = false) (e : Ev α) :
    e ∈ (exhaustive p n).1 ↔ sem p e := by
  induction p generalizing n with
  | pure a => simp [exhaustive, sem]
  | ub r => simp [exhaustive, sem]
  | choose w k ih =>
    by_cases hw : w ≤ n
    · simp only [exhaustive, hw, ite_true] at h ⊢
      simp only [List.any_map, List.any_eq_false, Function.comp_apply,
        Bool.not_eq_true] at h
      simp only [List.mem_flatMap, List.mem_map, sem]
      constructor
      · rintro ⟨_, ⟨b, _, rfl⟩, he⟩
        exact ⟨b, (ih b (n - w) (h b (mem_allBV b))).mp he⟩
      · rintro ⟨b, hb⟩
        exact ⟨_, ⟨b, mem_allBV b, rfl⟩,
          (ih b (n - w) (h b (mem_allBV b))).mpr hb⟩
    · simp [exhaustive, hw] at h

/-- Scripted mode returns a member of the semantic set. -/
theorem scripted_mem_sem (p : Prog α) (s : List Nat) (e : Ev α) (u : Bool)
    (h : scripted p s = some (e, u)) : sem p e := by
  induction p generalizing s u with
  | pure a => simp only [scripted, Option.some.injEq, Prod.mk.injEq] at h; simp [sem, h.1]
  | ub r => simp only [scripted, Option.some.injEq, Prod.mk.injEq] at h; simp [sem, h.1]
  | choose w k ih =>
    cases s with
    | nil => simp [scripted] at h
    | cons c cs =>
      simp only [scripted, Option.map_eq_some_iff] at h
      obtain ⟨⟨e', u'⟩, h1, h2⟩ := h
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, -⟩ := h2
      exact ⟨_, ih _ cs u' h1⟩

end Prog
end FirOwn
