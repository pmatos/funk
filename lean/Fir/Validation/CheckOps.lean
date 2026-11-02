import Fir.Validation.Check
import Fir.Validation.Graph

/-!
The check of a function first builds, once, what it looks up for each op:
the type of each value, where each value is defined, the first block with
each label, the graph, and where its paths start. The theorems after them
say what each holds, in terms of the rules' own definitions.
-/

namespace Fir

variable {d : Dialect}

/-- What the check of a function computes once, and looks up for each op. -/
structure FuncTables (d : Dialect) where
  /-- The type of each value of the function, at any depth: the type of its
  first definition (`Func.typeOf`). -/
  scope : Std.HashMap Name d.Ty
  /-- Every site where each value is defined among the function's top-level
  blocks (`Func.Defines`). -/
  sites : Std.HashMap Name (List DefSite)
  /-- The first block with each label (`Func.block?`). -/
  blocks : Std.HashMap Name (Block d)
  /-- The function's graph. -/
  graph : Std.HashMap Name (List Name)
  /-- Where every path starts: the entry's label. -/
  start : List Name

/-- Each definition of a value among the top-level blocks, with its site. -/
def Func.defSites (f : Func d) : List (Name × List DefSite) :=
  f.params.map (fun x => (x.1, [.param])) ++
    f.blocks.flatMap fun b =>
      b.params.map (fun x => (x.1, [.arg b.label])) ++
        b.body.zipIdx.flatMap fun (o, j) => o.results.map fun x => (x.1, [.result b.label j])

/-- The tables of a function, built from `all`, its blocks at any depth
(`Func.allBlocks`). Only the scope reaches into regions. -/
def Func.tables (f : Func d) (all : List (Block d)) : FuncTables d where
  scope := firsts (f.params ++ all.flatMap Block.defs)
  sites := grouped f.defSites
  blocks := firsts (f.blocks.map fun b => (b.label, b))
  graph := f.graph
  start := f.start

theorem Func.scope_eq (f : Func d) (x : Name) :
    (f.tables f.allBlocks).scope[x]? = f.typeOf x := by
  simp [Func.tables, getElem?_firsts, Func.typeOf, Func.defs]

theorem Func.scope_fun (f : Func d) :
    (fun x => (f.tables f.allBlocks).scope[x]?) = f.typeOf :=
  funext f.scope_eq

theorem Func.blocks_eq (f : Func d) (all : List (Block d)) (l : Name) :
    (f.tables all).blocks[l]? = f.block? l := by
  simp [Func.tables, getElem?_firsts, List.find?_map, Func.block?, Function.comp_def]

theorem Func.start_head? (f : Func d) (all : List (Block d)) :
    (f.tables all).start.head? = f.entryLabel? := by
  simp only [Func.tables, Func.start]
  cases f.entryLabel? <;> rfl

theorem Func.mem_sites (f : Func d) (all : List (Block d)) (x : Name) (s : DefSite) :
    s ∈ (f.tables all).sites.getD x [] ↔ f.Defines x s := by
  simp only [Func.tables, mem_getD_grouped, Func.defSites, List.mem_append, List.mem_map,
    List.mem_flatMap]
  cases s with
  | param =>
    simp only [Func.Defines, List.mem_map]
    constructor
    · rintro ⟨_, (⟨y, hy, rfl⟩ | ⟨b, _, ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩⟩), rfl, hs⟩
      · exact ⟨y, hy, rfl⟩
      · simp at hs
      · simp at hs
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, Or.inl ⟨y, hy, rfl⟩, rfl, List.mem_singleton_self _⟩
  | arg l =>
    simp only [Func.Defines, List.mem_map]
    constructor
    · rintro ⟨_, (⟨_, _, rfl⟩ | ⟨b, hb, ⟨y, hy, rfl⟩ | ⟨_, _, _, _, rfl⟩⟩), rfl, hs⟩
      · simp at hs
      · simp only [List.mem_singleton, DefSite.arg.injEq] at hs
        exact ⟨b, hb, hs.symm, y, hy, rfl⟩
      · simp at hs
    · rintro ⟨b, hb, rfl, y, hy, rfl⟩
      exact ⟨_, Or.inr ⟨b, hb, Or.inl ⟨y, hy, rfl⟩⟩, rfl, List.mem_singleton_self _⟩
  | result l j =>
    simp only [Func.Defines, List.mem_map]
    constructor
    · rintro ⟨_, (⟨_, _, rfl⟩ | ⟨b, hb, ⟨_, _, rfl⟩ | ⟨⟨o, k⟩, hk, y, hy, rfl⟩⟩), rfl, hs⟩
      · simp at hs
      · simp at hs
      · simp only [List.mem_singleton, DefSite.result.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ⟨b, hb, rfl, o, List.mem_zipIdx_iff_getElem?.mp hk, y, hy, rfl⟩
    · rintro ⟨b, hb, rfl, o, ho, y, hy, rfl⟩
      exact ⟨_, Or.inr ⟨b, hb, Or.inr ⟨(o, j), List.mem_zipIdx_iff_getElem?.mpr ho, y, hy, rfl⟩⟩,
        rfl, List.mem_singleton_self _⟩

/-!
# Uses and successors

A definition dominates a use as `Func.DominatesUse` says: a parameter
always, a block argument when its block dominates the use's, and an op's
result when it comes earlier in the use's block, or its block dominates the
use's. A use is in scope when the function defines the value among its
top-level blocks and each definition dominates the use.
-/

/-- Whether a definition at site `s` dominates a use by the op at index `i`
of block `l`, in a function with the graph `g` whose paths start at
`start`. -/
def siteDominates (g : Std.HashMap Name (List Name)) (start : List Name) (s : DefSite)
    (l : Name) (i : Nat) : Bool :=
  match s with
  | .param => true
  | .arg a => dominatesIn g start a l
  | .result a j => (a == l && decide (j < i)) || (a != l && dominatesIn g start a l)

/-- Why a definition of `x` at site `s` does not dominate a use in block `l`. -/
def DefSite.why (x l : Name) : DefSite → String
  | .param => valueRef x ++ " is a parameter"
  | .arg a => valueRef x ++ " is an argument of " ++ labelRef a ++ ", which does not dominate " ++
      labelRef l
  | .result a _ =>
    if a == l then valueRef x ++ " is used before it is defined"
    else valueRef x ++ " is defined in " ++ labelRef a ++ ", which does not dominate " ++ labelRef l

/-- The problems of a use of `x` by the op at index `i` of block `l`. `at_`
makes a problem about the op. -/
def useProblems (t : FuncTables d) (at_ : String → Problem) (l : Name) (i : Nat) (x : Name) :
    List Problem :=
  match t.sites.getD x [] with
  | [] =>
    if t.scope.contains x then [at_ (valueRef x ++ " is defined inside a region, and is not " ++
      "in scope here")]
    else [at_ (valueRef x ++ " is not defined in the function")]
  | s :: ss => (s :: ss).filterMap fun s =>
    if siteDominates t.graph t.start s l i then none else some (at_ (s.why x l))

variable [DecidableEq d.Ty]

/-- The problems of a successor `s` of an op. -/
def succProblems (t : FuncTables d) (at_ : String → Problem) (s : Succ) : List Problem :=
  (if t.start.head? = some s.label then
    [at_ ("no branch may go to the entry block " ++ labelRef s.label)] else []) ++
  match t.blocks[s.label]? with
  | none => [at_ ("successor " ++ labelRef s.label ++ " is not a block of the function")]
  | some tgt =>
    if sameLists (s.args.map (t.scope[·]?)) (tgt.params.map (some ·.2)) then []
    else [at_ ("successor " ++ labelRef s.label ++ " does not pass one value of the right " ++
      "type for each argument of the block")]

omit [DecidableEq d.Ty] in
theorem ite_nil_eq_nil {α : Type} {c : Prop} [Decidable c] {p : α} :
    ((if c then [] else [p]) : List α) = [] ↔ c := by
  split <;> simp_all

omit [DecidableEq d.Ty] in
theorem ite_none_eq_none {α : Type} {c : Prop} [Decidable c] {p : α} :
    (if c then none else some p) = none ↔ c := by
  split <;> simp_all

omit [DecidableEq d.Ty] in
theorem siteDominates_iff {f : Func d} {s : DefSite} {l : Name} {i : Nat}
    (hl : ∃ b ∈ f.blocks, b.label = l) :
    siteDominates f.graph f.start s l i = true ↔ f.DominatesUse s l i := by
  cases s <;> simp [siteDominates, Func.DominatesUse, Func.dominatesIn_iff hl]

omit [DecidableEq d.Ty] in
/-- The check of a use decides whether it is in scope. -/
theorem useProblems_eq_nil {f : Func d} {at_ : String → Problem} {l : Name} {i : Nat} {x : Name}
    (hl : ∃ b ∈ f.blocks, b.label = l) :
    useProblems (f.tables f.allBlocks) at_ l i x = [] ↔ f.InScope x l i := by
  have hs := f.mem_sites f.allBlocks x
  unfold useProblems Func.InScope
  split
  · rename_i h
    constructor
    · intro hp
      split at hp <;> simp at hp
    · rintro ⟨⟨s, hd⟩, _⟩
      rw [← hs, h] at hd
      simp at hd
  · rename_i s ss h
    rw [List.filterMap_eq_nil_iff]
    simp only [ite_none_eq_none]
    constructor
    · intro hall
      refine ⟨⟨s, (hs s).mp (h ▸ List.mem_cons_self ..)⟩, fun s' hd => ?_⟩
      exact (siteDominates_iff hl).mp (hall s' (h ▸ (hs s').mpr hd))
    · rintro ⟨_, hall⟩ s' hs'
      exact (siteDominates_iff hl).mpr (hall s' ((hs s').mp (h ▸ hs')))

/-- The check of a successor decides whether it is valid. -/
theorem succProblems_eq_nil {f : Func d} {at_ : String → Problem} {s : Succ} :
    succProblems (f.tables f.allBlocks) at_ s = [] ↔ f.SuccValid s := by
  unfold succProblems Func.SuccValid
  rw [List.append_eq_nil_iff, f.start_head?, f.blocks_eq]
  cases hb : f.block? s.label with
  | none => simp
  | some tgt => simp [sameLists_iff, Func.scope_eq]

variable [DialectSignature d] [DialectValidation d] [DecidableDialectValidation d]

/-!
# Ops

The check of an op follows `Func.OpValid`, rule by rule, in its order.
-/

/-- The problems of the op `o` at index `i` of block `b` of function `f`,
given `n`, the number of ops of `b`, which the caller counts once per
block. -/
def opProblems (lk : Lookup d) (f : Func d) (t : FuncTables d) (b : Block d) (n : Nat) (i : Nat)
    (o : Operation d) : List Problem :=
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
  o.uses.flatMap (useProblems t at_ b.label i) ++
  (symbolRefs o.op).filterMap (fun g => if (lk.symbols g).isSome then none else
    some (at_ ("the op refers to " ++ Text.printSymbol g ++ ", which names no function"))) ++
  (if validOp ⟨lk.symbols, f.results⟩ o.op then [] else
    [at_ "the op breaks its dialect's own rule"]) ++
  (if lk.hasLoc o.loc then [] else
    [at_ ("location reference @" ++ toString o.loc ++ " is not in the location table")])

omit [DecidableEq d.Ty] [DialectSignature d] [DialectValidation d]
  [DecidableDialectValidation d] in
theorem eq_beq_iff {a : Bool} {n m : Nat} : a = (n == m) ↔ (a = true ↔ n = m) := by
  cases a <;> by_cases h : n = m <;> simp [h]

omit [DecidableEq d.Ty] [DialectSignature d] [DialectValidation d]
  [DecidableDialectValidation d] in
theorem or_isEmpty_eq_true {a : Bool} {l : List Succ} :
    (a || l.isEmpty) = true ↔ (a = false → l = []) := by
  cases a <;> simp

/-- The check of an op decides `Func.OpValid`, for every op of a block of the
function. -/
theorem opProblems_eq_nil {lk : Lookup d} {ctx : ModuleContext d} {f : Func d} {b : Block d}
    {i : Nat} {o : Operation d} (h : lk.Agrees ctx) (hb : b ∈ f.blocks) :
    opProblems lk f (f.tables f.allBlocks) b b.body.length i o = [] ↔ f.OpValid ctx b i o := by
  have hl : ∃ b' ∈ f.blocks, b'.label = b.label := ⟨b, hb, rfl⟩
  simp only [opProblems, Func.OpValid, List.append_eq_nil_iff, ite_nil_eq_nil, sameLists_iff,
    Func.scope_fun, List.isEmpty_iff, beq_iff_eq, eq_beq_iff, or_isEmpty_eq_true,
    List.flatMap_eq_nil_iff, succProblems_eq_nil, useProblems_eq_nil hl,
    List.filterMap_eq_nil_iff, ite_none_eq_none, h.symbols, h.hasLoc, and_assoc]

end Fir
