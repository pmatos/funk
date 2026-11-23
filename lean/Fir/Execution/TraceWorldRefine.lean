import Fir.Execution.TraceEscapeLaws
import Fir.Execution.TraceObligations

/-!
# What the world gives, on traced states that refine others

An external call ends with the world's answer: its reply, whose pointers
name their allocations by their handles, and its actions on escaped memory
(`TraceM.ask`). Two laws let the traced layer compare a call that the
source makes with one that the target makes:

* _Reading back a pointer_ (`TraceState.fromWorldPtr`): a pointer that the
  world gives names its allocation by its handle. In the run it is a
  pointer into the allocation that the handle names, if that allocation is
  of the pointer's memory; a pointer without provenance stays as it is.
  Otherwise the world cannot give it. How a traced state reads back a
  pointer depends only on its escaped list.
* _The world's actions keep refinement_: from traced states that refine
  others, when the world can take its actions on the others, it can on the
  first, and the traced states they leave refine each other. A write lands
  in the same allocation, since both name it by the same handle, and
  memories that refine others give, for the same units, memories that
  refine theirs; an allocation that the world creates gets the same id in
  both; a free frees the same allocation, of the same kind and liveness.
-/

namespace Fir

open Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] (μ : Nat → Mem)

/-! # Reading back what the world gives -/

/-- The pointer `p` of the memory numbered `n` that the world gives, naming
its allocation by its handle, as a pointer of the run in the traced state
`s`, where the memory numbered `n` is `μ n`: itself when it has no
provenance, the allocation that its handle names when that allocation is
of its memory, and none otherwise. -/
def TraceState.fromWorldPtr (s : TraceState Mem unit) (n : Nat) (p : Pointer) : Option Pointer :=
  match p.prov with
  | none => some p
  | some h => match s.escaped[h]? with
    | some (x, a) => if x = μ n then some { p with prov := some a } else none
    | none => none

/-- Traced states with the same escaped list read back the world's pointers
alike. -/
theorem TraceState.fromWorldPtr_congr {s t : TraceState Mem unit} (h : s.escaped = t.escaped) :
    s.fromWorldPtr μ = t.fromWorldPtr μ := by
  funext n p
  unfold TraceState.fromWorldPtr
  rw [h]

/-! # The world's actions on traced states that refine others -/

/-- The world's action on traced states that refine others: when it can take
it on the others, it can on the first, and the traced states it leaves
refine each other. -/
theorem WorldAct.apply_isRefinedBy {s s' : TraceState Mem unit} (h : s ⊑ s') :
    ∀ (w : WorldAct) {t' : TraceState Mem unit}, w.apply μ s' = some t' →
      ∃ t, w.apply μ s = some t ∧ t ⊑ t'
  | .store hd o us, t', ht => by
    obtain ⟨hm, he⟩ := h
    simp only [WorldAct.apply, he, Option.bind_eq_bind] at ht ⊢
    cases hx : s'.escaped[hd]? with
    | none => simp [hx] at ht
    | some xa =>
      obtain ⟨x, a⟩ := xa
      simp only [hx, Option.bind_some] at ht ⊢
      cases hu : us.mapM (WUnit.resolve μ s'.escaped (unit x)) with
      | none => simp [hu] at ht
      | some us' =>
        simp only [hu, Option.bind_some] at ht ⊢
        rcases hm.store x ⟨some a, o⟩ (List.isRefinedBy_refl MemUnit.isRefinedBy_refl us') 1 with
          ⟨f, h₁, h₂⟩ | ⟨T, T', h₁, h₂, hT⟩
        · rw [h₂] at ht
          cases ht
        · rw [h₂] at ht
          cases ht
          exact ⟨{ mem := T, escaped := s'.escaped }, by rw [h₁], hT, rfl⟩
  | .alloc m n k, t', ht => by
    obtain ⟨hm, he⟩ := h
    simp only [WorldAct.apply, Option.some.injEq] at ht
    subst ht
    have hl : (s.mem.mem (μ m)).blocks.length = (s'.mem.mem (μ m)).blocks.length :=
      List.IsRefinedBy.length_eq (hm.2.1 (μ m))
    exact ⟨_, rfl, (hm.alloc (μ m) .heap n (2 ^ k)).2, by rw [he, hl]⟩
  | .free hd, t', ht => by
    obtain ⟨hm, he⟩ := h
    simp only [WorldAct.apply, he, Option.bind_eq_bind] at ht ⊢
    cases hx : s'.escaped[hd]? with
    | none => simp [hx] at ht
    | some xa =>
      obtain ⟨x, a⟩ := xa
      simp only [hx, Option.bind_some] at ht ⊢
      rcases List.IsRefinedBy.getElem? (hm.2.1 x) a with ⟨h₁, h₂⟩ | ⟨b, b', h₁, h₂, hb⟩
      · have h₂' : (s'.mem.mem x).blocks[a]? = none := h₂
        simp [h₂'] at ht
      · have h₁' : (s.mem.mem x).blocks[a]? = some b := h₁
        have h₂' : (s'.mem.mem x).blocks[a]? = some b' := h₂
        simp only [h₂', Option.bind_some] at ht
        simp only [h₁', Option.bind_some, hb.1, hb.2.2.1]
        split at ht
        · rename_i hc
          cases ht
          exact ⟨{ mem := s.mem.free x a, escaped := s'.escaped }, by simp [hc], hm.free x a, rfl⟩
        · cases ht

/-- The world's actions, in order, on traced states that refine others: when
it can take them on the others, it can on the first, and the traced states
they leave refine each other. -/
theorem WorldAct.applyAll_isRefinedBy :
    ∀ (ws : List WorldAct) {s s' t' : TraceState Mem unit}, s ⊑ s' →
      WorldAct.applyAll μ ws s' = some t' → ∃ t, WorldAct.applyAll μ ws s = some t ∧ t ⊑ t'
  | [], _, _, _, h, ht => by
    cases ht
    exact ⟨_, rfl, h⟩
  | w :: ws, s, s', t', h, ht => by
    simp only [WorldAct.applyAll] at ht ⊢
    cases hw : w.apply μ s' with
    | none => rw [hw] at ht; cases ht
    | some u' =>
      rw [hw] at ht
      obtain ⟨u, hu, hu'⟩ := WorldAct.apply_isRefinedBy μ h w hw
      obtain ⟨t, ht₁, ht₂⟩ := WorldAct.applyAll_isRefinedBy ws hu' ht
      exact ⟨t, by rw [hu]; exact ht₁, ht₂⟩

end Fir
