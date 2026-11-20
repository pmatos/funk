import FirRef.MachineModes
import Fir.Execution.NaNModes

/-!
`fir-ref run --exhaustive --nans` walks the spec's tree of a run as
`ChoiceTree.exploreNaN` does, trying a few NaNs at each NaN choice
(`docs/decisions/fir-ref-command-line.md#trying-a-few-nans`). As exhaustive
mode does in `FirRef.RunModes`, it walks the states of `FirRef.Machine` in a
loop of tail calls, with a work list of the states it has still to explore and
of each choice's values it has still to try, in the order the spec visits
them. So it takes no stack per step, per level of calls or per choice.

`Machine.exhaustiveNaN_eq` proves, for every dialect, that it gives what the
spec's walk of the run's tree gives. `FirRef.Run` registers it in place of
`Gpu.exhaustiveNaN` with `@[csimp]`.
-/

namespace FirRef

open Fir Memory

namespace Machine

variable {ε α : Type}

/-- The size of a tree as the walk that tries a few NaNs sees it, with the
NaNs `nans`: each leaf counts 1, each choice 2 and each edge from a choice
to the subtree of a value it tries 1. -/
def nanSize (nans : List Nat) : ChoiceTree ε α → Nat
  | .choose w c k => ((ChoiceTree.tryAt nans w c).1.map fun b => nanSize nans (k b) + 1).sum + 2
  | _ => 1

theorem nanSize_pos (nans : List Nat) : ∀ t : ChoiceTree ε α, 0 < nanSize nans t
  | .choose .. | .pure _ | .ub _ | .noOutcome _ => by simp only [nanSize]; omega

/-- The bits that the walk charges at a choice of `w` bits of the kind `c`,
without listing the values it tries: a choice past the budget lists none,
which for `freeze` of an `i64` would be 2^64 values. -/
def tryBits (nans : List Nat) (w : Nat) : ChoiceKind → Nat
  | .bits => w
  | .nan e => ChoiceTree.bitsFor (ChoiceTree.nanTries nans e w).length

theorem tryBits_eq (nans : List Nat) (w : Nat) (c : ChoiceKind) :
    tryBits nans w c = (ChoiceTree.tryAt nans w c).2.1 := by
  cases c <;> rfl

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DecidableEq d.Ty] [DialectCall d]
  {N : Type} [DecidableEq N] {unit : N → Nat}
  [DialectDenote d (StateT (Memories N unit) (ChoiceTree ε))] (M : Module d)

local notation "Mems" => Memories N unit

variable {R : Type} (fin : List (DVal d) → Memories N unit → R)

/-- Each leaf of a path that has made `made` choices more, `nan` of them
NaN choices, with both counted. -/
def shiftNaN (made nan : Nat) : Leaf d ε R × Nat × Nat → Leaf d ε R × Nat × Nat :=
  fun p => (p.1, p.2.1 + made, p.2.2 + nan)

/-- An entry of the work list: a state to explore, with its choice budget
and the choices and NaN choices made before it, or the values of a choice
still to try, with the budget and the counts that the state after each of
them starts from. -/
inductive NaNWork (d : Dialect) [TyDenote d.Ty] [DialectSignature d] (ε σ : Type) where
  | state (s : Cur d ε σ × List (Frame d)) (budget made nan : Nat)
  | values (w : Nat) (k : BitVec w → Cur d ε σ × List (Frame d)) (bs : List (BitVec w))
      (budget made nan : Nat)

/-- What the walk gives for a state: the spec's `ChoiceTree.exploreNaN` on
its tree. -/
def nanState (nans : List Nat) (s : Cur d ε Mems × List (Frame d)) (budget made nan : Nat) :
    Option (List (Leaf d ε R × Nat × Nat)) :=
  ((tree M fin s.1 s.2).exploreNaN nans budget).map (List.map (shiftNaN made nan))

/-- What the walk gives for an entry of the work list. -/
def nanExplored (nans : List Nat) : NaNWork d ε Mems → Option (List (Leaf d ε R × Nat × Nat))
  | .state s budget made nan => nanState M fin nans s budget made nan
  | .values _ k bs budget made nan =>
    ChoiceTree.collect (fun b => nanState M fin nans (k b) budget made nan) bs []

/-- A measure of an entry of the work list. -/
def NaNWork.size (nans : List Nat) : NaNWork d ε Mems → Nat
  | .state s _ _ _ => nanSize nans (tree M fin s.1 s.2)
  | .values _ k bs _ _ _ => (bs.map fun b => nanSize nans (tree M fin (k b).1 (k b).2) + 1).sum + 1

/-- A measure of the work list that each step of `exploreNaNFrom` lowers. -/
def nanWorkSize (nans : List Nat) (ps : List (NaNWork d ε Mems)) : Nat :=
  (ps.map (NaNWork.size M fin nans)).sum

set_option wf.preprocess false in
/-- The walk that tries a few NaNs, on a work list, after the leaves `acc`,
the last first: the spec's `ChoiceTree.collect` of `nanExplored` over the
work list. At a choice it tries the values one at a time, in order, and
stops at the first path over the budget, as the spec does. -/
def exploreNaNFrom (nans : List Nat) :
    List (NaNWork d ε Mems) → List (Leaf d ε R × Nat × Nat) → Option (List (Leaf d ε R × Nat × Nat))
  | [], acc => some acc.reverse
  | .state s budget made nan :: rest, acc => match _h : advance M fin s.1 s.2 with
    | .leaf l => exploreNaNFrom nans rest ((l, made, nan) :: acc)
    | .choose w c k =>
      if tryBits nans w c ≤ budget then
        let t := ChoiceTree.tryAt nans w c
        exploreNaNFrom nans (.values w k t.1 (budget - t.2.1) (made + 1) (nan + t.2.2) :: rest) acc
      else none
  | .values _ _ [] _ _ _ :: rest, acc => exploreNaNFrom nans rest acc
  | .values w k (b :: bs) budget made nan :: rest, acc =>
    exploreNaNFrom nans (.state (k b) budget made nan :: .values w k bs budget made nan :: rest) acc
termination_by ps => nanWorkSize M fin nans ps
decreasing_by
  · have := nanSize_pos nans (tree M fin s.1 s.2)
    simp only [nanWorkSize, NaNWork.size, List.map_cons, List.sum_cons]
    omega
  · have hs : nanSize nans (tree M fin s.1 s.2) =
        ((ChoiceTree.tryAt nans w c).1.map
          fun b => nanSize nans (tree M fin (k b).1 (k b).2) + 1).sum + 2 := by
      rw [tree_of_choose M fin _h]; rfl
    simp only [nanWorkSize, NaNWork.size, List.map_cons, List.sum_cons]
    omega
  · simp only [nanWorkSize, NaNWork.size, List.map_cons, List.sum_cons, List.map_nil,
      List.sum_nil]
    omega
  · simp only [nanWorkSize, NaNWork.size, List.map_cons, List.sum_cons]
    omega

omit [DialectSignature d] [DecidableEq d.Ty] [DialectCall d] [DecidableEq N]
  [DialectDenote d (StateT Mems (ChoiceTree ε))] in
theorem shiftNaN_shiftNaN (made nan k : Nat) :
    shiftNaN (d := d) (ε := ε) (R := R) made nan ∘ shiftNaN 1 k = shiftNaN (made + 1) (nan + k) := by
  funext p
  simp only [shiftNaN, Function.comp_apply, Prod.mk.injEq, true_and]
  omega

omit [DialectSignature d] [DecidableEq d.Ty] [DialectCall d] [DecidableEq N]
  [DialectDenote d (StateT Mems (ChoiceTree ε))] in
theorem exploreNaN_leafTree (nans : List Nat) (l : Leaf d ε R) (budget : Nat) :
    (leafTree l).exploreNaN nans budget = some [(l, 0, 0)] := by
  cases l <;> rfl

theorem exploreNaNFrom_eq (nans : List Nat) (ps : List (NaNWork d ε Mems))
    (acc : List (Leaf d ε R × Nat × Nat)) :
    exploreNaNFrom M fin nans ps acc = ChoiceTree.collect (nanExplored M fin nans) ps acc := by
  fun_induction exploreNaNFrom M fin nans ps acc with
  | case1 acc => rfl
  | case2 s budget made nan rest acc l h ih =>
    rw [ih, ChoiceTree.collect]
    have he : nanExplored M fin nans (.state s budget made nan) = some [(l, made, nan)] := by
      simp only [nanExplored, nanState]
      rw [tree_of_leaf M fin h, exploreNaN_leafTree]
      simp [shiftNaN]
    rw [he]
    rfl
  | case3 s budget made nan rest acc w c k h hw t ih =>
    rw [tryBits_eq] at hw
    rw [ih]
    simp only [ChoiceTree.collect]
    have hE : ∀ φ : Leaf d ε R × Nat × Nat → Leaf d ε R × Nat × Nat,
        ChoiceTree.collect (fun b => ((tree M fin (k b).1 (k b).2).exploreNaN nans (budget - t.2.1)).map
          (List.map φ)) t.1 [] =
        (ChoiceTree.collect (fun b => (tree M fin (k b).1 (k b).2).exploreNaN nans (budget - t.2.1))
          t.1 []).map (List.map φ) :=
      fun φ => collect_map_list _ φ _ []
    have hv : nanExplored M fin nans (.values w k t.1 (budget - t.2.1) (made + 1) (nan + t.2.2)) =
        ChoiceTree.collect (fun b => ((tree M fin (k b).1 (k b).2).exploreNaN nans
          (budget - t.2.1)).map (List.map (shiftNaN (made + 1) (nan + t.2.2)))) t.1 [] :=
      rfl
    have hs : nanExplored M fin nans (.state s budget made nan) =
        (ChoiceTree.collect (fun b => ((tree M fin (k b).1 (k b).2).exploreNaN nans
          (budget - t.2.1)).map (List.map (shiftNaN 1 t.2.2))) t.1 []).map
          (List.map (shiftNaN made nan)) := by
      simp only [nanExplored, nanState]
      rw [tree_of_choose M fin h]
      simp only [ChoiceTree.exploreNaN, t, ite_eq_left hw]
      rfl
    rw [hv, hs, hE, hE]
    cases ChoiceTree.collect (fun b => (tree M fin (k b).1 (k b).2).exploreNaN nans (budget - t.2.1))
      t.1 [] with
    | none => rfl
    | some L => simp only [Option.map_some, List.map_map, shiftNaN_shiftNaN]
  | case4 s budget made nan rest acc w c k h hw =>
    rw [tryBits_eq] at hw
    rw [ChoiceTree.collect]
    have h2 : nanExplored M fin nans (.state s budget made nan) = none := by
      simp only [nanExplored, nanState]
      rw [tree_of_choose M fin h]
      simp only [ChoiceTree.exploreNaN, ite_eq_right hw, Option.map_none]
    rw [h2]
  | case5 w k budget made nan rest acc ih =>
    rw [ih, ChoiceTree.collect]
    rfl
  | case6 w k b bs budget made nan rest acc ih =>
    rw [ih]
    simp only [ChoiceTree.collect, nanExplored]
    cases nanState M fin nans (k b) budget made nan with
    | none => rfl
    | some l =>
      simp only
      rw [collect_acc _ bs (l.reverseAux [])]
      cases ChoiceTree.collect (fun b => nanState M fin nans (k b) budget made nan) bs [] with
      | none => rfl
      | some L => simp [List.reverseAux_eq]

omit [DialectSignature d] [DecidableEq d.Ty] [DialectCall d] [DecidableEq N]
  [DialectDenote d (StateT Mems (ChoiceTree ε))] in
theorem map_shiftNaN_zero : ∀ l : List (Leaf d ε R × Nat × Nat), l.map (shiftNaN 0 0) = l
  | [] => rfl
  | _ :: l => by rw [List.map_cons, map_shiftNaN_zero l]; rfl

/-- The walk that tries a few NaNs on the run with memory of the function
`f` of the module `M` on `args` with `fuel` steps, a choice budget of
`budget` bits and the NaNs `nans`, by the machine, each return seen by
`fin`. -/
def exhaustiveNaNWith (f : Func d) (args : HVector toType (f.params.map (·.2)))
    (fuel budget : Nat) (nans : List Nat) : Option (List (Leaf d ε R × Nat × Nat)) :=
  match f.enter args.toDVals with
  | .error e => some [(.ok (.error e), 0, 0)]
  | .ok (body, env) =>
    exploreNaNFrom M fin nans [.state (start (N := N) (unit := unit) f fuel body env) budget 0 0] []

/-- The walk by the machine is the spec's `ChoiceTree.exploreNaN` on the
tree of the run with memory. -/
theorem exhaustiveNaNWith_eq (f : Func d) (args : HVector toType (f.params.map (·.2)))
    (fuel budget : Nat) (nans : List Nat) :
    exhaustiveNaNWith M fin f args fuel budget nans =
      (endTree (ε := ε) M fin f args fuel).exploreNaN nans budget := by
  unfold exhaustiveNaNWith
  rw [run_tree M fin f args fuel]
  cases f.enter args.toDVals with
  | error e => rfl
  | ok p =>
    show exploreNaNFrom M fin nans [.state (start f fuel p.1 p.2) budget 0 0] [] =
      (tree M fin (start (ε := ε) (N := N) (unit := unit) f fuel p.1 p.2).1 []).exploreNaN nans
        budget
    rw [exploreNaNFrom_eq M fin, ChoiceTree.collect]
    simp only [nanExplored, nanState]
    cases (tree M fin (start (ε := ε) (N := N) (unit := unit) f fuel p.1 p.2).1 []).exploreNaN
      nans budget <;> simp [ChoiceTree.collect, map_shiftNaN_zero]

/-- The walk that tries a few NaNs on the run with memory of the function
`f`, by the machine, each return seen as its values. -/
def exhaustiveNaN (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat)
    (nans : List Nat) : Option (List (Leaf d ε × Nat × Nat)) :=
  exhaustiveNaNWith (ε := ε) (unit := unit) M (fun vs _ => vs) f args fuel budget nans

theorem exhaustiveNaN_eq (f : Func d) (args : HVector toType (f.params.map (·.2)))
    (fuel budget : Nat) (nans : List Nat) :
    exhaustiveNaN (ε := ε) (unit := unit) M f args fuel budget nans =
      (f.memTree unit M args fuel).exploreNaN nans budget := by
  rw [memTree_eq]; exact exhaustiveNaNWith_eq M _ f args fuel budget nans

end Machine

end FirRef
