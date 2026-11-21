import FirRef.RunModes

/-!
The modes of `FirRef.RunModes` on the run of a function, from the state
that it starts from, the memories `S₀` that hold the run's starting
allocations with a frame entered: scripted, sampled and exhaustive mode by the machine,
each the spec's walk of the tree of the run with memory
(`docs/decisions/fir-ref-fast-paths.md#running`). A return is seen by a
function `fin` of its values and of the memories at its end: `fir-ref run`
sees it as its end (`FirRef.Run`), and the modes that the core's and
`gpu`'s `@[csimp]` theorems name see it as its values, the tree of the
spec's `Func.memTree`.
-/

namespace FirRef

open Fir Memory

namespace Machine

variable {ε : Type} {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DecidableEq d.Ty]
  [DialectCall d] {N : Type} [DecidableEq N] {unit : N → Nat}
  [DialectDenote d (StateT (Memories N unit) (ChoiceTree ε))] (M : Module d)

local notation "Mems" => Memories N unit

variable (S₀ : Memories N unit) {R : Type} (fin : List (DVal d) → Memories N unit → R)

/-- The tree of a run with memory of the function `f` of the module `M` on
`args` with `fuel` steps, from the memories `S₀`, where a return of the
values `vs` with the memories `S` at its end is seen as `fin vs S`. -/
def endTree (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    ChoiceTree ε (Except Stuck (Result R)) :=
  endWith fin <$> runAt (f.run M (m := StateT Mems (ChoiceTree ε)) args fuel) S₀

/-- The spec's tree of a run with memory is the tree that sees a return as
its values. -/
theorem memTree_eq (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    f.memTree unit (ε := ε) S₀ M args fuel = endTree (unit := unit) (ε := ε) M S₀ (fun vs _ => vs) f args fuel := by
  show Prod.fst <$> _ = endWith _ <$> _
  rw [endWith_vals]
  rfl

/-- The tree of a run with memory of a function, as the state that it
starts from: the function's ops, from the memories `S₀` with a frame
entered. -/
theorem run_tree (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    endTree (ε := ε) M S₀ fin f args fuel = match f.enter args.toDVals with
      | .error e => .pure (.error e)
      | .ok (body, env) =>
        tree M fin (.ops fuel f (Bindings.ofEnv env) body S₀.enter) [] := by
  show endWith fin <$> runAt (f.run M args fuel) S₀ = _
  unfold Func.run
  rw [runAt_bind]
  cases f.enter args.toDVals with
  | error e => rfl
  | ok p =>
    show endWith fin <$> runAt (inFrame (Func.runOps M fuel f p.2 p.1) >>= _) S₀ =
      endWith fin <$> kont M []
        (runAt (Func.runOps M fuel f (Bindings.ofEnv p.2).toEnv p.1) S₀.enter)
    rw [runOps_congr fuel f _ p.2 p.1 (same_toEnv (Bindings.agrees_ofEnv p.2)), runAt_bind,
      runAt_inFrame, ChoiceTree.bind_assoc]
    congr 1

/-- The state that a run with memory of `f` starts from, when its entry
fits its arguments. -/
abbrev start (f : Func d) (fuel : Nat) (body : List (Operation d)) (env : Env d) :
    Cur d ε Mems × List (Frame d) :=
  (.ops fuel f (Bindings.ofEnv env) body S₀.enter, [])

/-! # The modes on a function's run -/

/-- Scripted mode on the run with memory of the function `f` of the module
`M` on `args` with `fuel` steps, by the machine, each return seen by
`fin`. -/
def scriptedWith {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ) :
    Except (ChoiceTree.Misfit σ) (Leaf d ε R × Nat) :=
  match f.enter args.toDVals with
  | .error e => (ChoiceTree.pure (.error e) : ChoiceTree ε _).script read cs 0
  | .ok (body, env) => scriptFrom M fin read (start S₀ f fuel body env) cs 0

/-- Scripted mode by the machine is the spec's `ChoiceTree.script` on the
tree of the run with memory. -/
theorem scriptedWith_eq {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ) :
    scriptedWith (ε := ε) M S₀ fin read f args fuel cs = (endTree M S₀ fin f args fuel).script read cs 0 := by
  unfold scriptedWith
  rw [run_tree M S₀ fin f args fuel]
  cases f.enter args.toDVals with
  | error e => rfl
  | ok p => exact scriptFrom_eq M fin read (start S₀ f fuel p.1 p.2) cs 0

/-- Sampled mode on the run with memory of the function `f` of the module
`M` on `args` with `fuel` steps, by the machine, each return seen by
`fin`. -/
def sampledWith {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    Leaf d ε R × List ChoiceTree.Chosen :=
  match f.enter args.toDVals with
  | .error e => (.ok (.error e), [])
  | .ok (body, env) => sampleFrom M fin draw (start S₀ f fuel body env) g []

/-- Sampled mode by the machine is the spec's `ChoiceTree.sample` on the
tree of the run with memory. -/
theorem sampledWith_eq {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    sampledWith (ε := ε) M S₀ fin draw f args fuel g = (endTree M S₀ fin f args fuel).sample draw g := by
  unfold sampledWith
  rw [run_tree M S₀ fin f args fuel]
  cases f.enter args.toDVals with
  | error e => rfl
  | ok p => simp [sampleFrom_eq]

/-- Exhaustive mode on the run with memory of the function `f` of the
module `M` on `args` with `fuel` steps and a choice budget of `budget`
bits, by the machine, each return seen by `fin`. -/
def exhaustiveWith (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) :
    Option (List (Leaf d ε R × Nat)) :=
  match f.enter args.toDVals with
  | .error e => some [(.ok (.error e), 0)]
  | .ok (body, env) =>
    exploreFrom M fin [.state (start S₀ f fuel body env) budget 0] []

/-- Exhaustive mode by the machine is the spec's `ChoiceTree.explore` on
the tree of the run with memory. -/
theorem exhaustiveWith_eq (f : Func d) (args : HVector toType (f.params.map (·.2)))
    (fuel budget : Nat) :
    exhaustiveWith (ε := ε) M S₀ fin f args fuel budget = (endTree M S₀ fin f args fuel).explore budget := by
  unfold exhaustiveWith
  rw [run_tree M S₀ fin f args fuel]
  cases f.enter args.toDVals with
  | error e => rfl
  | ok p =>
    show exploreFrom M fin [.state (start S₀ f fuel p.1 p.2) budget 0] [] =
      (tree M fin (start (ε := ε) S₀ f fuel p.1 p.2).1 []).explore budget
    rw [exploreFrom_eq M fin, ChoiceTree.collect]
    simp only [explored, exploredState]
    cases (tree M fin (start (ε := ε) S₀ f fuel p.1 p.2).1 []).explore
      budget <;> simp [ChoiceTree.collect, map_shift_zero]

/-! # The modes that see a return as its values -/

/-- Scripted mode on the run with memory of the function `f`, by the
machine, each return seen as its values. -/
def scripted {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ) :
    Except (ChoiceTree.Misfit σ) (Leaf d ε × Nat) :=
  scriptedWith (ε := ε) (unit := unit) M S₀ (fun vs _ => vs) read f args fuel cs

theorem scripted_eq {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ) :
    scripted (ε := ε) (unit := unit) M S₀ read f args fuel cs =
      (f.memTree unit S₀ M args fuel).script read cs 0 := by
  rw [memTree_eq]; exact scriptedWith_eq M S₀ _ read f args fuel cs

/-- Sampled mode on the run with memory of the function `f`, by the
machine, each return seen as its values. -/
def sampled {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    Leaf d ε × List ChoiceTree.Chosen :=
  sampledWith (ε := ε) (unit := unit) M S₀ (fun vs _ => vs) draw f args fuel g

theorem sampled_eq {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    sampled (ε := ε) (unit := unit) M S₀ draw f args fuel g =
      (f.memTree unit S₀ M args fuel).sample draw g := by
  rw [memTree_eq]; exact sampledWith_eq M S₀ _ draw f args fuel g

/-- Exhaustive mode on the run with memory of the function `f`, by the
machine, each return seen as its values. -/
def exhaustive (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) :
    Option (List (Leaf d ε × Nat)) :=
  exhaustiveWith (ε := ε) (unit := unit) M S₀ (fun vs _ => vs) f args fuel budget

theorem exhaustive_eq (f : Func d) (args : HVector toType (f.params.map (·.2)))
    (fuel budget : Nat) :
    exhaustive (ε := ε) (unit := unit) M S₀ f args fuel budget =
      (f.memTree unit S₀ M args fuel).explore budget := by
  rw [memTree_eq]; exact exhaustiveWith_eq M S₀ _ f args fuel budget

end Machine

end FirRef
