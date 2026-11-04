import FirRef.Machine

/-!
`fir-ref run` walks the spec's tree of a run in one of three modes, the
spec's `Core.scripted`, `Core.exhaustive` and `Core.sampled`
(ADR-2026-10-30-2218, ADR-2026-10-31-0002). Each of them builds the tree
with `Func.runOps`, which takes stack per step and per level of calls, and
`ChoiceTree.sample` and `ChoiceTree.explore` add stack per choice. Here,
each mode walks the states of `FirRef.Machine` instead, in loops whose
recursive calls are tail calls: `Machine.advance` takes the steps between
two choices, scripted and sampled modes keep what they have read or drawn
in an accumulator, and exhaustive mode keeps the states it has still to
explore, and each choice's values it has still to visit, on a work list,
in the order that the spec visits them. So no mode takes stack per step,
per level of calls or per choice.

`Machine.scripted_eq`, `Machine.exhaustive_eq` and `Machine.sampled_eq`
prove, for every dialect, that each mode by the machine gives what the
spec's walk of the run's tree gives, from `Machine.advance_tree`.
`FirRef.Run` registers the three in place of the core dialect's modes with
`@[csimp]`, before `fir-ref run`'s code, since only `fir-ref`'s command
line may name the core dialect here (ADR-2026-10-30-1450,
ADR-2026-11-03-0600, ADR-2026-11-04-2132).
-/

namespace FirRef

open Fir

namespace Machine

variable {ε α : Type}

/-- The size of a tree: each leaf counts 1, each choice 2 and each edge
from a choice to one of its subtrees 1. -/
def treeSize : ChoiceTree ε α → Nat
  | .choose w k => ((ChoiceTree.allBits w).map fun b => treeSize (k b) + 1).sum + 2
  | _ => 1

theorem le_sum_of_mem : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum
  | _ :: _, _, .head _ => by simp only [List.sum_cons]; omega
  | _ :: _, _, .tail _ h => by have := le_sum_of_mem h; simp only [List.sum_cons]; omega

theorem treeSize_lt {w : Nat} (k : BitVec w → ChoiceTree ε α) (b : BitVec w) :
    treeSize (k b) < treeSize (.choose w k) := by
  have := le_sum_of_mem (List.mem_map.2 ⟨b, ChoiceTree.mem_allBits b, rfl⟩ :
    treeSize (k b) + 1 ∈ (ChoiceTree.allBits w).map fun b => treeSize (k b) + 1)
  simp only [treeSize]
  omega

theorem treeSize_pos : ∀ t : ChoiceTree ε α, 0 < treeSize t
  | .choose .. | .pure _ | .ub _ | .noOutcome _ => by simp only [treeSize]; omega

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DecidableEq d.Ty] [DialectCall d]
  [DialectDenote d (ChoiceTree ε)] (M : Module d)

theorem tree_of_choose {c : Cur d ε} {st : List (Frame d)} {w : Nat}
    {k : BitVec w → Cur d ε × List (Frame d)} (h : advance M c st = .choose w k) :
    tree M c st = .choose w fun b => tree M (k b).1 (k b).2 := by
  rw [← advance_tree, h]; rfl

theorem tree_of_leaf {c : Cur d ε} {st : List (Frame d)} {l : Leaf d ε}
    (h : advance M c st = .leaf l) : tree M c st = leafTree l := by
  rw [← advance_tree, h]; rfl

/-! # Scripted mode -/

/-- Scripted mode from a state, after `made` choices: the spec's
`ChoiceTree.script` on the state's tree. -/
def scriptFrom {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (s : Cur d ε × List (Frame d))
    (cs : List σ) (made : Nat) : Except (ChoiceTree.Misfit σ) (Leaf d ε × Nat) :=
  match advance M s.1 s.2, cs with
  | .leaf l, cs => (leafTree l).script read cs made
  | .choose w _, [] => .error (.short made w)
  | .choose w k, x :: cs => match read w x with
    | some b => scriptFrom read (k b) cs (made + 1)
    | none => .error (.unread made w x)
termination_by cs.length

theorem scriptFrom_eq {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (s : Cur d ε × List (Frame d)) (cs : List σ) (made : Nat) :
    scriptFrom M read s cs made = (tree M s.1 s.2).script read cs made := by
  fun_induction scriptFrom M read s cs made with
  | case1 s made l cs h => rw [tree_of_leaf M h]
  | case2 s made w k h => rw [tree_of_choose M h]; rfl
  | case3 s made w k x cs h b hb ih => rw [ih, tree_of_choose M h, ChoiceTree.script, hb]
  | case4 s made w k x cs h hb => rw [tree_of_choose M h, ChoiceTree.script, hb]

/-! # Sampled mode -/

omit [DialectSignature d] [DecidableEq d.Ty] [DialectCall d] [DialectDenote d (ChoiceTree ε)] in
theorem sample_leafTree {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (l : Leaf d ε) (g : γ) :
    (leafTree l).sample draw g = (l, []) := by
  cases l <;> rfl

/-- Sampled mode from a state, with the values drawn so far in `acc`, the
last first: the spec's `ChoiceTree.sample` on the state's tree, after
them. -/
def sampleFrom {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (s : Cur d ε × List (Frame d))
    (g : γ) (acc : List ChoiceTree.Chosen) : Leaf d ε × List ChoiceTree.Chosen :=
  match _h : advance M s.1 s.2 with
  | .leaf l => (l, acc.reverse)
  | .choose w k =>
    let dr := draw w g
    sampleFrom draw (k dr.1) dr.2 (⟨w, dr.1⟩ :: acc)
termination_by treeSize (tree M s.1 s.2)
decreasing_by rw [tree_of_choose M _h]; exact treeSize_lt (fun b => tree M (k b).1 (k b).2) _

theorem sampleFrom_eq {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (s : Cur d ε × List (Frame d)) (g : γ) (acc : List ChoiceTree.Chosen) :
    sampleFrom M draw s g acc =
      (((tree M s.1 s.2).sample draw g).1, acc.reverse ++ ((tree M s.1 s.2).sample draw g).2) := by
  fun_induction sampleFrom M draw s g acc with
  | case1 s g acc l h => rw [tree_of_leaf M h, sample_leafTree]; simp
  | case2 s g acc w k h dr ih => rw [ih, tree_of_choose M h]; simp [ChoiceTree.sample, dr]

/-! # Exhaustive mode -/

section Collect

variable {β γ : Type}

theorem collect_acc (g : β → Option (List γ)) :
    ∀ (xs : List β) (acc : List γ),
      ChoiceTree.collect g xs acc = (ChoiceTree.collect g xs []).map (acc.reverse ++ ·)
  | [], acc => by simp [ChoiceTree.collect]
  | x :: xs, acc => by
    simp only [ChoiceTree.collect]
    split
    · rename_i l _
      rw [collect_acc g xs (l.reverseAux acc), collect_acc g xs (l.reverseAux [])]
      simp [List.reverseAux_eq, Option.map_map, Function.comp_def]
    · rfl

theorem collect_map_list (g : β → Option (List γ)) (φ : γ → γ) :
    ∀ (xs : List β) (acc : List γ),
      ChoiceTree.collect (fun x => (g x).map (List.map φ)) xs (acc.map φ) =
        (ChoiceTree.collect g xs acc).map (List.map φ)
  | [], acc => by simp [ChoiceTree.collect]
  | x :: xs, acc => by
    simp only [ChoiceTree.collect]
    cases hg : g x with
    | none => rfl
    | some l =>
      simp only [Option.map_some]
      rw [← collect_map_list g φ xs (l.reverseAux acc)]
      simp [List.reverseAux_eq]

end Collect

/-- Each leaf of a path that has made `made` choices more, with the
choices counted. -/
def shift (made : Nat) : Leaf d ε × Nat → Leaf d ε × Nat := fun p => (p.1, p.2 + made)

/-- An entry of exhaustive mode's work list: a state to explore, with its
choice budget and the choices made before it, or the values of a choice
still to visit, with the budget and the count of choices that the state
after each of them starts from. -/
inductive Work (d : Dialect) [TyDenote d.Ty] [DialectSignature d] (ε : Type) where
  | state (s : Cur d ε × List (Frame d)) (budget made : Nat)
  | values (w : Nat) (k : BitVec w → Cur d ε × List (Frame d)) (bs : List (BitVec w))
      (budget made : Nat)

/-- What exhaustive mode gives for a state, with its choice budget and the
choices made before it: the spec's `ChoiceTree.explore` on its tree. -/
def exploredState (s : Cur d ε × List (Frame d)) (budget made : Nat) :
    Option (List (Leaf d ε × Nat)) :=
  ((tree M s.1 s.2).explore budget).map (List.map (shift made))

/-- What exhaustive mode gives for an entry of the work list: for the
values of a choice, the spec's `ChoiceTree.collect` of the states after
them. -/
def explored : Work d ε → Option (List (Leaf d ε × Nat))
  | .state s budget made => exploredState M s budget made
  | .values _ k bs budget made =>
    ChoiceTree.collect (fun b => exploredState M (k b) budget made) bs []

/-- A measure of an entry of the work list. -/
def Work.size : Work d ε → Nat
  | .state s _ _ => treeSize (tree M s.1 s.2)
  | .values _ k bs _ _ => (bs.map fun b => treeSize (tree M (k b).1 (k b).2) + 1).sum + 1

/-- A measure of the work list that each step of `exploreFrom` lowers. -/
def workSize (ps : List (Work d ε)) : Nat :=
  (ps.map (Work.size M)).sum

set_option wf.preprocess false in
/-- Exhaustive mode on a work list, after the leaves `acc`, the last first:
the spec's `ChoiceTree.collect` of `explored` over the work list. At a
choice it visits the values one at a time, from zero up, and so goes on
from a value only when it gets to it and stops at the first path over the
budget, as the spec does. -/
def exploreFrom : List (Work d ε) → List (Leaf d ε × Nat) → Option (List (Leaf d ε × Nat))
  | [], acc => some acc.reverse
  | .state s budget made :: rest, acc => match _h : advance M s.1 s.2 with
    | .leaf l => exploreFrom rest ((l, made) :: acc)
    | .choose w k =>
      if w ≤ budget then
        exploreFrom (.values w k (ChoiceTree.allBits w) (budget - w) (made + 1) :: rest) acc
      else none
  | .values _ _ [] _ _ :: rest, acc => exploreFrom rest acc
  | .values w k (b :: bs) budget made :: rest, acc =>
    exploreFrom (.state (k b) budget made :: .values w k bs budget made :: rest) acc
termination_by ps => workSize M ps
decreasing_by
  · have := treeSize_pos (tree M s.1 s.2)
    simp only [workSize, Work.size, List.map_cons, List.sum_cons]
    omega
  · have hs : treeSize (tree M s.1 s.2) =
        ((ChoiceTree.allBits w).map fun b => treeSize (tree M (k b).1 (k b).2) + 1).sum + 2 := by
      rw [tree_of_choose M _h]; rfl
    simp only [workSize, Work.size, List.map_cons, List.sum_cons]
    omega
  · simp only [workSize, Work.size, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
    omega
  · simp only [workSize, Work.size, List.map_cons, List.sum_cons]
    omega

omit [DialectSignature d] [DecidableEq d.Ty] [DialectCall d] [DialectDenote d (ChoiceTree ε)] in
theorem shift_shift (made : Nat) : shift (d := d) (ε := ε) made ∘ shift 1 = shift (made + 1) := by
  funext p
  simp only [shift, Function.comp_apply, Prod.mk.injEq, true_and]
  omega

omit [DialectSignature d] [DecidableEq d.Ty] [DialectCall d] [DialectDenote d (ChoiceTree ε)] in
theorem explore_leafTree (l : Leaf d ε) (budget : Nat) :
    (leafTree l).explore budget = some [(l, 0)] := by
  cases l <;> rfl

theorem exploreFrom_eq (ps : List (Work d ε)) (acc : List (Leaf d ε × Nat)) :
    exploreFrom M ps acc = ChoiceTree.collect (explored M) ps acc := by
  fun_induction exploreFrom M ps acc with
  | case1 acc => rfl
  | case2 s budget made rest acc l h ih =>
    rw [ih, ChoiceTree.collect]
    have he : explored M (.state s budget made) = some [(l, made)] := by
      simp only [explored, exploredState]
      rw [tree_of_leaf M h, explore_leafTree]
      simp [shift]
    rw [he]
    rfl
  | case3 s budget made rest acc w k h hw ih =>
    rw [ih]
    simp only [ChoiceTree.collect]
    have hE : ∀ φ : Leaf d ε × Nat → Leaf d ε × Nat,
        ChoiceTree.collect (fun b => ((tree M (k b).1 (k b).2).explore (budget - w)).map
          (List.map φ)) (ChoiceTree.allBits w) [] =
        (ChoiceTree.collect (fun b => (tree M (k b).1 (k b).2).explore (budget - w))
          (ChoiceTree.allBits w) []).map (List.map φ) :=
      fun φ => collect_map_list _ φ _ []
    have hv : explored M (.values w k (ChoiceTree.allBits w) (budget - w) (made + 1)) =
        ChoiceTree.collect (fun b => ((tree M (k b).1 (k b).2).explore (budget - w)).map
          (List.map (shift (made + 1)))) (ChoiceTree.allBits w) [] :=
      rfl
    have hs : explored M (.state s budget made) =
        (ChoiceTree.collect (fun b => ((tree M (k b).1 (k b).2).explore (budget - w)).map
          (List.map (shift 1))) (ChoiceTree.allBits w) []).map (List.map (shift made)) := by
      simp only [explored, exploredState]
      rw [tree_of_choose M h]
      simp only [ChoiceTree.explore, ite_eq_left hw]
      rfl
    rw [hv, hs, hE, hE]
    cases ChoiceTree.collect (fun b => (tree M (k b).1 (k b).2).explore (budget - w))
      (ChoiceTree.allBits w) [] with
    | none => rfl
    | some L => simp only [Option.map_some, List.map_map, shift_shift]
  | case4 s budget made rest acc w k h hw =>
    rw [ChoiceTree.collect]
    have h2 : explored M (.state s budget made) = none := by
      simp only [explored, exploredState]
      rw [tree_of_choose M h]
      simp only [ChoiceTree.explore, ite_eq_right hw, Option.map_none]
    rw [h2]
  | case5 w k budget made rest acc ih =>
    rw [ih, ChoiceTree.collect]
    rfl
  | case6 w k b bs budget made rest acc ih =>
    rw [ih]
    simp only [ChoiceTree.collect, explored]
    cases exploredState M (k b) budget made with
    | none => rfl
    | some l =>
      simp only
      rw [collect_acc _ bs (l.reverseAux [])]
      cases ChoiceTree.collect (fun b => exploredState M (k b) budget made) bs [] with
      | none => rfl
      | some L => simp [List.reverseAux_eq]

omit [DialectSignature d] [DecidableEq d.Ty] [DialectCall d] [DialectDenote d (ChoiceTree ε)] in
theorem map_shift_zero : ∀ l : List (Leaf d ε × Nat), l.map (shift 0) = l
  | [] => rfl
  | _ :: l => by rw [List.map_cons, map_shift_zero l]; rfl

/-- The spec's run of a function, as the state that it starts from. -/
theorem run_tree (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    (f.run M (m := ChoiceTree ε) args fuel).run = match f.enter args.toDVals with
      | .error e => .pure (.error e)
      | .ok (body, env) => tree M (.ops fuel f env body) [] := by
  unfold Func.run
  cases f.enter args.toDVals with
  | error e => rfl
  | ok p => rfl

/-! # The modes on a function's run -/

/-- Scripted mode on the run of the function `f` of the module `M` on
`args` with `fuel` steps, by the machine. -/
def scripted {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ) :
    Except (ChoiceTree.Misfit σ) (Leaf d ε × Nat) :=
  match f.enter args.toDVals with
  | .error e => (ChoiceTree.pure (.error e) : ChoiceTree ε _).script read cs 0
  | .ok (body, env) => scriptFrom M read (.ops fuel f env body, []) cs 0

/-- Scripted mode by the machine is the spec's `ChoiceTree.script` on the
tree of the run. -/
theorem scripted_eq {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ) :
    scripted (ε := ε) M read f args fuel cs =
      (f.run M (m := ChoiceTree ε) args fuel).run.script read cs 0 := by
  unfold scripted
  rw [run_tree M f args fuel]
  cases f.enter args.toDVals with
  | error e => rfl
  | ok p => exact scriptFrom_eq M read (.ops fuel f p.2 p.1, []) cs 0

/-- Sampled mode on the run of the function `f` of the module `M` on `args`
with `fuel` steps, by the machine. -/
def sampled {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    Leaf d ε × List ChoiceTree.Chosen :=
  match f.enter args.toDVals with
  | .error e => (.ok (.error e), [])
  | .ok (body, env) => sampleFrom M draw (.ops fuel f env body, []) g []

/-- Sampled mode by the machine is the spec's `ChoiceTree.sample` on the
tree of the run. -/
theorem sampled_eq {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    sampled (ε := ε) M draw f args fuel g =
      (f.run M (m := ChoiceTree ε) args fuel).run.sample draw g := by
  unfold sampled
  rw [run_tree M f args fuel]
  cases f.enter args.toDVals with
  | error e => rfl
  | ok p => simp [sampleFrom_eq]

/-- Exhaustive mode on the run of the function `f` of the module `M` on
`args` with `fuel` steps and a choice budget of `budget` bits, by the
machine. -/
def exhaustive (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) :
    Option (List (Leaf d ε × Nat)) :=
  match f.enter args.toDVals with
  | .error e => some [(.ok (.error e), 0)]
  | .ok (body, env) => exploreFrom M [.state (.ops fuel f env body, []) budget 0] []

/-- Exhaustive mode by the machine is the spec's `ChoiceTree.explore` on
the tree of the run. -/
theorem exhaustive_eq (f : Func d) (args : HVector toType (f.params.map (·.2)))
    (fuel budget : Nat) :
    exhaustive (ε := ε) M f args fuel budget =
      (f.run M (m := ChoiceTree ε) args fuel).run.explore budget := by
  unfold exhaustive
  rw [run_tree M f args fuel]
  cases f.enter args.toDVals with
  | error e => rfl
  | ok p =>
    show exploreFrom M [.state (.ops fuel f p.2 p.1, []) budget 0] [] =
      (tree M (.ops fuel f p.2 p.1) []).explore budget
    rw [exploreFrom_eq M, ChoiceTree.collect]
    simp only [explored, exploredState]
    cases (tree (ε := ε) M (.ops fuel f p.2 p.1) []).explore budget <;>
      simp [ChoiceTree.collect, map_shift_zero]

end Machine

end FirRef
