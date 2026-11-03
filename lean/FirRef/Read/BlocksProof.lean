import FirRef.Read.Blocks

/-!
`blocksLoop` reads what the spec's readers of blocks, ops and regions read,
and fails where they fail: `blocksLoop_eq`, by induction on the loop, one
equation of the spec's readers per case. Each case unfolds the meaning of
the frames before and after the step and rewrites the spec's readers by
their equations until both sides are the same.
-/

namespace FirRef

open Fir Fir.Text Cursor

variable {σ : Type} [Cursor σ]

/-- Unfolds `bRun` and `bFinish` and reduces binds on known results. -/
macro "b_norm" : tactic => `(tactic| simp only [bRun, bFinish, V_ok, V_error, okBind, errorBind,
  pure_bind, bind_assoc, List.reverse_nil, List.nil_append, List.append_nil, List.reverse_cons,
  List.append_assoc, List.singleton_append, List.cons_append])

theorem blocksLoop_eq (s : σ) (fs : List BFrame) : V (blocksLoop s fs) = bRun (view s) fs := by
  fun_induction blocksLoop s fs with
  | case1 s => rfl
  | case2 s done fs l pos s₁ h params s₂ hh ih =>
    rw [ih, view_of_uncons h]
    simp only [bRun]
    rw [U_readBlocks_label, ← blockHeadC_eq, hh]
    b_norm
  | case3 s done fs l pos s₁ h e hh =>
    rw [view_of_uncons h]
    simp only [bRun]
    rw [U_readBlocks_label, ← blockHeadC_eq, hh]
    rfl
  | case4 s done hn =>
    simp only [bRun]
    rw [U_readBlocks_nil (fun l => not_head (hn l))]
    b_norm
  | case5 s done hd rs fs s₁ he hn ih =>
    simp only [List.unattach_reverse, List.unattach_attach] at ih
    rw [ih]
    simp only [bRun]
    rw [U_readBlocks_nil (fun l => not_head (hn l))]
    simp only [okBind, bFinish]
    rw [← expectC_eq, he]
    b_norm
  | case6 s done hd rs fs e he hn =>
    simp only [bRun]
    rw [U_readBlocks_nil (fun l => not_head (hn l))]
    simp only [okBind, bFinish]
    rw [← expectC_eq, he]
    rfl
  | case7 s done fs hn h0 hr =>
    simp only [bRun]
    rw [U_readBlocks_nil (fun l => not_head (hn l))]
    rcases fs with _ | ⟨_ | _ | _, fs⟩ <;>
      first | rfl | exact absurd rfl h0 | exact absurd rfl (hr _ _ _)
  | case8 s l params done fs n p s₁ h hd s₂ hh ih =>
    rw [ih, view_of_uncons h]
    simp only [bRun]
    rw [U_readOps_value, U_readOpWithResults, ← opWithResultsHeadC_eq, hh]
    b_norm
  | case9 s l params done fs n p s₁ h e hh =>
    rw [view_of_uncons h]
    simp only [bRun]
    rw [U_readOps_value, U_readOpWithResults, ← opWithResultsHeadC_eq, hh]
    rfl
  | case10 s l params done fs w p s₁ h hd s₂ hh ih =>
    rw [ih, view_of_uncons h]
    simp only [bRun]
    rw [U_readOps_word, U_readOpBody, ← opBodyHeadC_eq, hh]
    b_norm
  | case11 s l params done fs w p s₁ h e hh =>
    rw [view_of_uncons h]
    simp only [bRun]
    rw [U_readOps_word, U_readOpBody, ← opBodyHeadC_eq, hh]
    rfl
  | case12 s l params done bs fs hv hw ih =>
    simp only [List.unattach_reverse, List.unattach_attach] at ih
    rw [ih]
    simp only [bRun]
    rw [U_readOps_nil (fun n => not_head (hv n)) (fun w => not_head (hw w))]
    b_norm
  | case13 s l params done fs hv hw hb =>
    simp only [bRun]
    rw [U_readOps_nil (fun n => not_head (hv n)) (fun w => not_head (hw w))]
    rcases fs with _ | ⟨_ | _ | _, fs⟩ <;> first | rfl | exact absurd rfl (hb _ _)
  | case14 s hd done fs pos s₁ h ih =>
    rw [ih, view_of_uncons h]
    simp only [bRun]
    rw [U_readRegions_lbrace]
    b_norm
  | case15 s hd rs loc s₁ hl l params os fs hn ih =>
    simp only [List.unattach_reverse, List.unattach_attach] at ih
    rw [ih]
    simp only [bRun]
    rw [U_readRegions_nil (not_head hn)]
    simp only [okBind]
    rw [← readOpLocC_eq, hl]
    b_norm
  | case16 s hd rs fs loc s₁ hl hn ho =>
    simp only [bRun]
    rw [U_readRegions_nil (not_head hn)]
    simp only [okBind]
    rw [← readOpLocC_eq, hl]
    rcases fs with _ | ⟨_ | _ | _, fs⟩ <;> first | rfl | exact absurd rfl (ho _ _ _ _)
  | case17 s hd rs fs e hl hn =>
    simp only [bRun]
    rw [U_readRegions_nil (not_head hn)]
    simp only [okBind]
    rw [← readOpLocC_eq, hl]
    rfl

end FirRef
