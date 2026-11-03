import Fir.Validation.CheckFuncs
import FirRef.Dominance.Query

/-!
`fir-ref` checks a function with `FirRef.problemsIn`, not with the spec's
`Func.problemsIn` (#55). The spec decides each use whose definition is in
another block with its own search of the function's graph, `dominatesIn`,
so a function of `V` blocks with `U` such uses takes time in `O(U · V)`.
`problemsIn` builds the function's dominator tree once, with
`dominance` (`FirRef.Dominance.Query`), and answers each use from it.

The copies below are the spec's `siteDominates`, `useProblems`,
`opProblems` and `Func.problemsIn`, word for word, but for the function that
decides dominance, which they take as an argument. The theorem
`problemsIn_eq_problemsIn` proves `problemsIn` equal to the spec's, problems
and their order included, and `@[csimp]` makes Lean compile every later
call of `Func.problemsIn` as a call of `problemsIn` (ADR-2026-10-30-1450,
ADR-2026-10-30-1742). The rest of the check stays the spec's.
-/

namespace FirRef

open Fir Dom

variable {d : Dialect}

/-- `siteDominates`, with dominance decided by `dom`. -/
def siteDominatesWith (dom : Name → Name → Bool) (s : DefSite) (l : Name) (i : Nat) : Bool :=
  match s with
  | .param => true
  | .arg a => dom a l
  | .result a j => (a == l && decide (j < i)) || (a != l && dom a l)

theorem siteDominatesWith_eq (g : Graph) (start : List Name) :
    siteDominatesWith (dominatesIn g start) = siteDominates g start := by
  funext s l i
  cases s <;> rfl

/-- `useProblems`, with dominance decided by `dom`. -/
def useProblemsWith (dom : Name → Name → Bool) (t : FuncTables d) (at_ : String → Problem)
    (l : Name) (i : Nat) (x : Name) : List Problem :=
  match t.sites.getD x [] with
  | [] =>
    if t.scope.contains x then [at_ (valueRef x ++ " is defined inside a region, and is not " ++
      "in scope here")]
    else [at_ (valueRef x ++ " is not defined in the function")]
  | s :: ss => (s :: ss).filterMap fun s =>
    if siteDominatesWith dom s l i then none else some (at_ (s.why x l))

theorem useProblemsWith_eq (t : FuncTables d) :
    useProblemsWith (dominatesIn t.graph t.start) t = useProblems t := by
  funext at_ l i x
  simp only [useProblemsWith, useProblems, siteDominatesWith_eq]
  split <;> rename_i h <;> simp only [h]

/-- The dominator tree decides dominance in the function's graph as the
spec's search does. -/
theorem dominance_tables (f : Func d) (all : List (Block d)) :
    dominatesBy (dominance (f.tables all).graph f.entryLabel?) =
      dominatesIn (f.tables all).graph (f.tables all).start :=
  dominance_eq _ _

variable [DialectSignature d] [DialectValidation d] [DecidableEq d.Ty]
  [DecidableDialectValidation d]

/-- `opProblems`, with dominance decided by `dom`. -/
def opProblemsWith (dom : Name → Name → Bool) (lk : Lookup d) (f : Func d) (t : FuncTables d)
    (b : Block d) (n : Nat) (i : Nat) (o : Operation d) : List Problem :=
  let at_ (message : String) : Problem :=
    { message, func := f.name, block := b.label, op := i, loc := o.loc }
  let last := i + 1 == n
  (if o.regions.isEmpty then [] else [at_ "the op owns a region: no op may own one yet"]) ++
  (if sameLists (o.operands.map (t.scope[·]?)) ((sig o.op).map some) then [] else
    [at_ (if o.operands.length = (sig o.op).length then
        "an operand of the op is not of the type that its op instance takes"
      else "the op has " ++ toString o.operands.length ++ " operands, and its op instance " ++
        "takes " ++ toString (sig o.op).length)]) ++
  (if sameLists (o.results.map (·.2)) (returnTypes o.op) then [] else
    [at_ (if o.results.length = (returnTypes o.op).length then
        "a result of the op is not of the type that its op instance gives"
      else "the op has " ++ toString o.results.length ++ " results, and its op instance " ++
        "gives " ++ toString (returnTypes o.op).length)]) ++
  (if isTerminator o.op == last then [] else
    [at_ (if last then "block " ++ labelRef b.label ++ " does not end with a terminator"
      else "the op ends a block, and is not the last op of " ++ labelRef b.label)]) ++
  (if o.succs.length == succCount o.op then [] else
    [at_ ("the op has " ++ toString o.succs.length ++ " successors, and its op instance has " ++
      toString (succCount o.op))]) ++
  (if isTerminator o.op || o.succs.isEmpty then [] else
    [at_ "the op is not a terminator, and only terminators have successors"]) ++
  o.succs.flatMap (succProblems t at_) ++
  o.uses.flatMap (useProblemsWith dom t at_ b.label i) ++
  (symbolRefs o.op).filterMap (fun g => if (lk.symbols g).isSome then none else
    some (at_ ("the op refers to " ++ Text.printSymbol g ++ ", which names no function"))) ++
  (if validOp ⟨lk.symbols, f.results⟩ o.op then [] else
    [at_ "the op breaks its dialect's own rule"]) ++
  (if lk.hasLoc o.loc then [] else
    [at_ ("location reference @" ++ toString o.loc ++ " is not in the location table")])

theorem opProblemsWith_eq (lk : Lookup d) (f : Func d) (t : FuncTables d) (b : Block d)
    (n i : Nat) (o : Operation d) :
    opProblemsWith (dominatesIn t.graph t.start) lk f t b n i o = opProblems lk f t b n i o := by
  simp only [opProblemsWith, opProblems, useProblemsWith_eq]

/-- `Func.problemsIn`, deciding dominance with the function's dominator
tree, built once. -/
def problemsIn (lk : Lookup d) (f : Func d) (all : List (Block d)) : List Problem :=
  let t := f.tables all
  let tree := dominance t.graph f.entryLabel?
  let defs := f.params ++ all.flatMap Block.defs
  let reached := reachedIn t.graph t.start
  f.entryProblems ++
  f.blocks.filterMap (fun b => if reached.contains b.label then none else
    some (f.blockProblem b ("block " ++ labelRef b.label ++ " is not reachable from the entry"))) ++
  (repeats (f.blocks.map (·.label))).map (fun l =>
    { message := "label " ++ labelRef l ++ " names more than one block", func := f.name,
      block := l, loc := (t.blocks[l]?.bind (·.body.head?)).map (·.loc) }) ++
  (repeats (defs.map (·.1))).map (fun x =>
    f.problem ("value " ++ valueRef x ++ " is defined more than once")) ++
  defs.filterMap (fun x => if isName x.1 then none else
    some (f.problem ("value name " ++ Text.quote x.1 ++ " is not one or more name characters"))) ++
  all.filterMap (fun b => if isName b.label then none else
    some (f.blockProblem b ("label " ++ Text.quote b.label ++
      " is not one or more name characters"))) ++
  f.results.filterMap (fun ty => if validTy ty then none else
    some (f.problem "a result type of the function is not valid")) ++
  defs.filterMap (fun x => if validTy x.2 then none else
    some (f.problem ("the type of " ++ valueRef x.1 ++ " is not valid"))) ++
  f.blocks.filterMap (fun b => if b.body ≠ [] then none else
    some (f.blockProblem b ("block " ++ labelRef b.label ++ " holds no ops"))) ++
  f.blocks.flatMap (fun b => let n := b.body.length
    b.body.zipIdx.flatMap fun (o, i) => opProblemsWith (dominatesBy tree) lk f t b n i o)

@[csimp] theorem problemsIn_eq_problemsIn : @Func.problemsIn = @problemsIn := by
  funext d _ _ _ _ lk f all
  have h : ∀ b n i o, opProblemsWith (dominatesBy (dominance (f.tables all).graph
      f.entryLabel?)) lk f (f.tables all) b n i o = opProblems lk f (f.tables all) b n i o :=
    fun b n i o => by
      rw [dominance_tables]
      exact opProblemsWith_eq lk f (f.tables all) b n i o
  simp only [Func.problemsIn, problemsIn, h]

end FirRef
