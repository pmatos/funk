import Fir.Validation.CheckModule
import FirRef.PrintModule

/-!
`fir-ref validate` runs the spec's validation check, `Module.problems`, at
any depth of nesting (#36). The check walks a function's nested blocks only
once, through `Func.allBlocks`, and the spec defines that walk by mutual
recursion, once per level of regions and once per block of a list. Here,
`allBlocks` lists the same blocks with an explicit stack of frames, in a
loop whose recursive calls are tail calls, so it takes no stack per level.
`allBlocks_eq_allBlocks` proves the two equal, and `@[csimp]` makes Lean
compile every later call of `Func.allBlocks` as a call of `allBlocks`
(ADR-2026-10-30-1450, ADR-2026-10-30-1742).

The spec compiles `Func.problems` and `Module.problems` before that
theorem exists, so their compiled code calls the spec's walk. `funcProblems`
and `moduleProblems` are copies of them, compiled after it and proved equal
by `rfl`, and two more `@[csimp]` theorems make `fir-ref` call the copies.
The rest of the check, `Func.problemsIn`, takes the list of blocks as an
argument, walks only lists, and keeps its own compiled code.
-/

namespace FirRef

open Fir

variable {d : Dialect}

/-- What is left to list of a function's blocks. -/
inductive Walk (d : Dialect) where
  /-- Blocks, with the blocks of their ops' regions. -/
  | blocks (bs : List (Block d))
  /-- The blocks of the regions of ops. -/
  | ops (os : List (Operation d))
  /-- The blocks of regions. -/
  | regions (rs : List (Region d))

/-- The blocks that a frame stands for, by the spec's walk. -/
def Walk.blocksOf : Walk d → List (Block d)
  | .blocks bs => Block.allBlocks bs
  | .ops os => Operation.regionBlocks os
  | .regions rs => Region.allBlocks rs

/-- A measure of a frame that each step of `walk` lowers. -/
def Walk.weight : Walk d → Nat
  | .blocks bs => blocksWeight bs + 1
  | .ops os => opsWeight os + 1
  | .regions rs => regionsWeight rs + 1

/-- A measure of a stack of frames. -/
def walksWeight : List (Walk d) → Nat
  | [] => 0
  | w :: ws => w.weight + walksWeight ws

/-- Lists the blocks of a stack of frames after `acc`, which holds the blocks
listed so far, last first. -/
def walk (acc : List (Block d)) : List (Walk d) → List (Block d)
  | [] => acc.reverse
  | .blocks [] :: ws => walk acc ws
  | .blocks (b :: bs) :: ws => walk (b :: acc) (.ops b.body :: .blocks bs :: ws)
  | .ops [] :: ws => walk acc ws
  | .ops (o :: os) :: ws => walk acc (.regions o.regions :: .ops os :: ws)
  | .regions [] :: ws => walk acc ws
  | .regions (r :: rs) :: ws => walk acc (.blocks r.blocks :: .regions rs :: ws)
termination_by ws => walksWeight ws
decreasing_by
  all_goals simp only [walksWeight, Walk.weight, blocksWeight_cons, regionsWeight_cons,
    opsWeight, opWeight_eq, blocksWeight, regionsWeight]
  all_goals omega

theorem allBlocks_cons (b : Block d) (bs : List (Block d)) :
    Block.allBlocks (b :: bs) = b :: Operation.regionBlocks b.body ++ Block.allBlocks bs := by
  cases b; simp [Block.allBlocks]

theorem regionBlocks_cons (o : Operation d) (os : List (Operation d)) :
    Operation.regionBlocks (o :: os) = Region.allBlocks o.regions ++ Operation.regionBlocks os := by
  cases o; simp [Operation.regionBlocks]

theorem regionAllBlocks_cons (r : Region d) (rs : List (Region d)) :
    Region.allBlocks (r :: rs) = Block.allBlocks r.blocks ++ Region.allBlocks rs := by
  cases r; simp [Region.allBlocks]

/-- The loop lists the blocks that its frames stand for, after those it has
listed. -/
theorem walk_eq (acc : List (Block d)) (ws : List (Walk d)) :
    walk acc ws = acc.reverse ++ ws.flatMap Walk.blocksOf := by
  fun_induction walk acc ws <;>
    simp_all [Walk.blocksOf, allBlocks_cons, regionBlocks_cons, regionAllBlocks_cons,
      Block.allBlocks, Operation.regionBlocks, Region.allBlocks]

/-- The blocks of a function at any depth, as `Func.allBlocks` lists them,
with no stack per level. -/
def allBlocks (f : Func d) : List (Block d) := walk [] [.blocks f.blocks]

@[csimp] theorem allBlocks_eq_allBlocks : @Func.allBlocks = @allBlocks := by
  funext d f
  simp [allBlocks, walk_eq, Walk.blocksOf, Func.allBlocks]

variable [DialectSignature d] [DialectValidation d] [DecidableEq d.Ty]
  [DecidableDialectValidation d]

/-- `Func.problems`, compiled after `allBlocks_eq_allBlocks`. -/
def funcProblems (lk : Lookup d) (f : Func d) : List Problem :=
  f.problemsIn lk f.allBlocks

@[csimp] theorem problems_eq_funcProblems : @Func.problems = @funcProblems := rfl

/-- `Module.problems`, compiled after `problems_eq_funcProblems`. -/
def moduleProblems (m : Module d) : List Problem :=
  let lk := m.lookup
  (repeats (m.funcs.map (·.name))).map (fun s =>
    { message := "the symbol " ++ Text.printSymbol s ++ " names more than one item", func := s }) ++
  m.locs.problems ++
  m.funcs.flatMap (·.problems lk)

@[csimp] theorem problems_eq_moduleProblems : @Module.problems = @moduleProblems := rfl

end FirRef
