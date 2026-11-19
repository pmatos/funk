import Fir.Execution.ObserveEnd

/-!
# Laws of the end of a return

Refinement of the ends of returns is a preorder: the renaming of every
allocation to itself shows an end in itself, and when one renaming shows
`s` in `m` and another shows `m` in `t`, the first then the second shows
`s` in `t`.

The second needs a fact about the middle end `m`: a pointer of `s` that is
not dangling is renamed to one that is not dangling in `m`, since the two
allocations are seen in each other, so they have the same liveness, or
neither is an allocation the run made. And the pointer it is renamed to is
in `m`'s returned values, or in the units of a live allocation of `m`
that the second renaming renames, so the second renaming renames it too.

When the source returns no pointer and nothing escaped, the end of its
return is refined by another exactly when its returned values are, and
nothing escaped in the other.
-/

namespace Fir

open Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] {μ : Nat → Mem}

/-! # Pointers under two renamings -/

/-- Under the renaming of every allocation to itself, a pointer is seen as
itself, or as poison when it is dangling. -/
theorem Renaming.ptr_id (S : Memories Mem unit) (n : Nat) (p : Pointer) :
    Renaming.id.ptr μ S n p = none ∨ Renaming.id.ptr μ S n p = some p := by
  obtain ⟨prov, o⟩ := p
  cases prov with
  | none => exact .inr rfl
  | some a =>
    unfold Renaming.ptr
    by_cases h : S.freed (μ n) a <;> simp [h, Renaming.id]

/-- The renaming of every allocation to itself renames every pointer that is
not dangling. -/
theorem Renaming.id_covers (S : Memories Mem unit) (n : Nat) (p : Pointer) :
    Renaming.id.Covers μ S n p := fun _ _ _ => rfl

/-- Two allocations seen in each other are both freed, or neither is. -/
theorem Memory.Block.OptSeenIn.freed_eq {ar : AddrRule} {f : Nat → Pointer → Option Pointer}
    {S T : Memories Mem unit} {x : Mem} {a a' : AllocId}
    (h : Block.OptSeenIn ar f ((S.mem x).blocks[a]?) ((T.mem x).blocks[a']?)) :
    S.freed x a = T.freed x a' := by
  unfold Memories.freed
  revert h
  cases (S.mem x).blocks[a]? <;> cases (T.mem x).blocks[a']? <;> intro h
  · rfl
  · exact h.elim
  · exact h.elim
  · simp only [h.2.2.1]

/-- Under one renaming then another, a pointer that the first renames
unless it is dangling is poison, or seen as the second sees its image under
the first, when the first renames only allocations whose images are freed
just when they are. -/
theorem Renaming.ptr_comp {S M : Memories Mem unit} {R₁ R₂ : Renaming Mem} {n : Nat} {p : Pointer}
    (hc : R₁.Covers μ S n p) (hf : ∀ x a a', R₁ x a = some a' → S.freed x a = M.freed x a') :
    (R₁.comp R₂).ptr μ S n p = none ∨
      (R₁.comp R₂).ptr μ S n p = (R₁.ptr μ S n p).bind (R₂.ptr μ M n) := by
  obtain ⟨prov, o⟩ := p
  cases prov with
  | none => exact .inr rfl
  | some a =>
    by_cases hfr : S.freed (μ n) a
    · left
      simp [Renaming.ptr, hfr]
    · obtain ⟨a₁, ha₁⟩ := Option.isSome_iff_exists.1 (hc a rfl (by simpa using hfr))
      have hM : M.freed (μ n) a₁ = false := by
        rw [← hf _ _ _ ha₁]
        simpa using hfr
      right
      simp [Renaming.ptr, Renaming.comp, hfr, ha₁, hM]

/-- One renaming then another renames a pointer that the first renames,
unless it is dangling, when the second renames its image under the first. -/
theorem Renaming.Covers.comp {S M : Memories Mem unit} {R₁ R₂ : Renaming Mem} {n : Nat}
    {p : Pointer} (hc : R₁.Covers μ S n p)
    (hf : ∀ x a a', R₁ x a = some a' → S.freed x a = M.freed x a')
    (h₂ : ∀ q, R₁.ptr μ S n p = some q → R₂.Covers μ M n q) : (R₁.comp R₂).Covers μ S n p := by
  intro a hp hfr
  obtain ⟨a₁, ha₁⟩ := Option.isSome_iff_exists.1 (hc a hp hfr)
  have hq : R₁.ptr μ S n p = some { p with prov := some a₁ } := by
    simp [Renaming.ptr, hp, hfr, ha₁]
  have hM : M.freed (μ n) a₁ = false := by
    rw [← hf _ _ _ ha₁]
    exact hfr
  have := h₂ _ hq a₁ rfl hM
  simpa [Renaming.comp, ha₁] using this

/-- Replacing the pointers of a value that a renaming covers, under the
renaming then another, refines less than replacing them under the first,
then under the second. -/
theorem HasPtrs.map_comp_le {W : Type} [HRefinement W W] [HasPtrs W] {S M : Memories Mem unit}
    {R₁ R₂ : Renaming Mem} (v : W) (hc : ∀ n p, (n, p) ∈ HasPtrs.ptrs v → R₁.Covers μ S n p)
    (hf : ∀ x a a', R₁ x a = some a' → S.freed x a = M.freed x a') :
    HasPtrs.map ((R₁.comp R₂).ptr μ S) v ⊑
      HasPtrs.map (R₂.ptr μ M) (HasPtrs.map (R₁.ptr μ S) v) := by
  rw [HasPtrs.map_map]
  exact HasPtrs.map_le _ _ v fun n p hp => Renaming.ptr_comp (hc n p hp) hf

/-! # Allocations seen in each other -/

section

variable {u : Nat} {ar : AddrRule}

/-- An allocation that is a block is seen in one that is a block too. -/
theorem Memory.Block.OptSeenIn.some_left {f : Nat → Pointer → Option Pointer} {b : Block u} :
    ∀ {o : Option (Block u)}, Block.OptSeenIn ar f (some b) o → ∃ b', o = some b' ∧ b.SeenIn ar f b'
  | some b', h => ⟨b', rfl, h⟩
  | none, h => h.elim

/-- An allocation seen in a second, which is seen in a third, is seen in the
third, when replacing its units' pointers by `f₃` refines less than by `f₁`
then `f₂`. -/
theorem Memory.Block.OptSeenIn.trans {f₁ f₂ f₃ : Nat → Pointer → Option Pointer} :
    ∀ {o₁ o₂ o₃ : Option (Block u)}, Block.OptSeenIn ar f₁ o₁ o₂ → Block.OptSeenIn ar f₂ o₂ o₃ →
      (∀ b, o₁ = some b → b.live →
        HasPtrs.map f₃ b.units ⊑ HasPtrs.map f₂ (HasPtrs.map f₁ b.units)) →
      Block.OptSeenIn ar f₃ o₁ o₃
  | none, none, none, _, _, _ => trivial
  | some b, some _, some _, h₁, h₂, h =>
    ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
      h₁.2.2.2.1.trans h₂.2.2.2.1, ar.trans h₁.2.2.2.2.1 h₂.2.2.2.2.1, fun hl =>
      List.isRefinedBy_trans MemUnit.isRefinedBy_trans (h b rfl hl)
        (List.isRefinedBy_trans MemUnit.isRefinedBy_trans (HasPtrs.map_mono _ (h₁.2.2.2.2.2 hl))
          (h₂.2.2.2.2.2 (h₁.2.2.1 ▸ hl)))⟩
  | none, some _, _, h, _, _ | some _, none, _, h, _, _ => h.elim
  | none, none, some _, _, h, _ | some _, some _, none, _, h, _ => h.elim

end

/-! # Refinement of the ends of returns -/

namespace End

variable {ar : AddrRule} {V : Type} [HRefinement V V] [HasPtrs V]

/-- The renaming of every allocation to itself shows an end in itself:
refinement of the ends of returns is reflexive. -/
theorem isRefinedBy_refl (s : End unit μ ar V) : s ⊑ s := by
  have hle : ∀ {W : Type} [HRefinement W W] [HasPtrs W] (v : W),
      HasPtrs.map (Renaming.id.ptr μ s.mem) v ⊑ v := fun v => by
    have := HasPtrs.map_le (Renaming.id.ptr μ s.mem) (fun _ p => some p) v
      fun n p _ => Renaming.ptr_id s.mem n p
    rwa [HasPtrs.map_some] at this
  refine ⟨Renaming.id, Renaming.id_injective, rfl, fun i e he => ⟨e, he, rfl, rfl⟩,
    fun n p _ => Renaming.id_covers _ n p, hle s.vals, fun x a a' ha => ?_⟩
  cases ha
  refine ⟨?_, fun _ _ _ n p _ => Renaming.id_covers _ n p⟩
  cases (s.mem.mem x).blocks[a]? with
  | none => exact trivial
  | some b => exact ⟨rfl, rfl, rfl, rfl, ar.refl _, fun _ => hle b.units⟩

/-- When one renaming shows `s` in `m` and another shows `m` in `t`, the first
then the second shows `s` in `t`: refinement of the ends of returns is
transitive when refinement of the returned values is. -/
theorem isRefinedBy_trans (hV : ∀ {a b c : V}, a ⊑ b → b ⊑ c → a ⊑ c)
    {s m t : End unit μ ar V} (h₁ : s ⊑ m) (h₂ : m ⊑ t) : s ⊑ t := by
  obtain ⟨R₁, hi₁, hl₁, he₁, hc₁, hv₁, hb₁⟩ := h₁
  obtain ⟨R₂, hi₂, hl₂, he₂, hc₂, hv₂, hb₂⟩ := h₂
  have hf : ∀ x a a', R₁ x a = some a' → s.mem.freed x a = m.mem.freed x a' :=
    fun x a a' ha => (hb₁ x a a' ha).1.freed_eq
  refine ⟨R₁.comp R₂, hi₁.comp hi₂, hl₁.trans hl₂, fun i e he => ?_,
    fun n p hp => (hc₁ n p hp).comp hf fun q hq => hc₂ n q (HasPtrs.ptrs_le _ hv₁ hp hq),
    hV (HasPtrs.map_comp_le s.vals hc₁ hf) (hV (HasPtrs.map_mono _ hv₁) hv₂),
    fun x a a₂ ha => ?_⟩
  · obtain ⟨e', he', h1, h2⟩ := he₁ i e he
    obtain ⟨e'', he'', h1', h2'⟩ := he₂ i e' he'
    refine ⟨e'', he'', h1.trans h1', ?_⟩
    show (R₁ e.1 e.2).bind (R₂ e.1) = _
    rw [h2]
    show R₂ e.1 e'.2 = _
    rw [h1, h2']
  · obtain ⟨a₁, ha₁, ha₂⟩ : ∃ a₁, R₁ x a = some a₁ ∧ R₂ x a₁ = some a₂ := by
      simpa [Renaming.comp, Option.bind_eq_some_iff] using ha
    obtain ⟨hs₁, hcv₁⟩ := hb₁ x a a₁ ha₁
    obtain ⟨hs₂, hcv₂⟩ := hb₂ x a₁ a₂ ha₂
    have hcov : ∀ b, (s.mem.mem x).blocks[a]? = some b → b.live →
        ∀ n p, (n, p) ∈ HasPtrs.ptrs b.units → (R₁.comp R₂).Covers μ s.mem n p := by
      intro b hb hl n p hp
      have hs := hs₁
      rw [hb] at hs
      obtain ⟨b₁, hb₁', hs⟩ := hs.some_left
      exact (hcv₁ b hb hl n p hp).comp hf fun q hq =>
        hcv₂ b₁ hb₁' (hs.2.2.1 ▸ hl) n q (HasPtrs.ptrs_le _ (hs.2.2.2.2.2 hl) hp hq)
    exact ⟨hs₁.trans hs₂ fun b hb hl => HasPtrs.map_comp_le b.units (hcv₁ b hb hl) hf, hcov⟩

/-- When the source returns no pointer and nothing escaped, the end of its
return is refined by another exactly when its returned values are, and
nothing escaped in the other. -/
theorem isRefinedBy_iff_vals (hV : ∀ {a b c : V}, a ⊑ b → b ⊑ c → a ⊑ c)
    {s t : End unit μ ar V} (hp : HasPtrs.ptrs s.vals = []) (he : s.escaped = []) :
    s ⊑ t ↔ s.vals ⊑ t.vals ∧ t.escaped = [] := by
  have hle : ∀ f, s.vals ⊑ HasPtrs.map f s.vals ∧ HasPtrs.map f s.vals ⊑ s.vals := fun f => by
    have h₁ := HasPtrs.map_le (fun _ p => some p) f s.vals (by simp [hp])
    have h₂ := HasPtrs.map_le f (fun _ p => some p) s.vals (by simp [hp])
    rw [HasPtrs.map_some] at h₁ h₂
    exact ⟨h₁, h₂⟩
  constructor
  · rintro ⟨R, -, hl, -, -, hv, -⟩
    exact ⟨hV (hle _).1 hv, List.eq_nil_of_length_eq_zero (by rw [← hl, he]; rfl)⟩
  · rintro ⟨hv, het⟩
    refine ⟨fun _ _ => none, (by intro _ _ _ _ h; cases h), (by rw [he, het]), fun i e h => ?_,
      (by simp [hp]), hV (hle _).2 hv, (by intro _ _ _ h; cases h)⟩
    rw [he] at h
    simp at h

end End

end Fir
