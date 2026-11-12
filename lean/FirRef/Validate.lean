import Fir.Validation.CheckModule
import Fir.Validation.DialectSet
import FirRef.Dominance
import FirRef.LocTable
import FirRef.PrintModule
import FirRef.Tables
import FirRef.AttrWalk

/-!
`fir-ref validate` runs the spec's validation check, `Module.problems`, at
any depth of nesting (#36). The check walks a function's nested blocks only
once, through `Func.allBlocks`, and the spec defines that walk by mutual
recursion, once per level of regions and once per block of a list. Here,
`allBlocks` lists the same blocks with an explicit stack of frames, in a
loop whose recursive calls are tail calls, so it takes no stack per level.
`allBlocks_eq_allBlocks` proves the two equal, and `@[csimp]` makes Lean
compile every later call of `Func.allBlocks` as a call of `allBlocks`
(ADR-2026-10-30-1450).

The spec compiles `Func.problems`, `SymbolTable.problems` and
`Module.problems` before that theorem exists, so their compiled code calls
the spec's walk. `funcProblems`, `tableProblems` and `moduleProblems` are
copies of them, compiled after it and proved equal by `rfl`, and more
`@[csimp]` theorems make `fir-ref` call the copies. `moduleProblems` lists
the module's symbol tables with `FirRef.Tables`'s walk, imported first,
which takes no stack per level of nested modules.
The rest of the check, `Func.problemsIn`, takes the list of blocks as an
argument and walks only lists. `FirRef.Dominance`, imported first, replaces
it with a copy that decides dominance with a dominator tree built at most
once per function, so the copies here call that one (#55). `moduleProblems`
checks the location table with `LocTable.problems`, which
`FirRef.LocTable`, imported first too, replaces with a check that takes no
stack per entry of the table or per reference of a location (#136).

The spec's instances `Decidable m.Valid` and `Decidable (f.Valid ctx)` are
compiled before these theorems too, and `decide` inlines an instance as its
own module compiled it, so they run the spec's walk. `decidableValid` and
`decidableFuncValid` are the same instances, word for word, compiled after
the theorems and proved equal to the spec's by `rfl`. Their priority puts
them first wherever this module is imported, so there `decide m.Valid` and
`decide (f.Valid ctx)` run `moduleProblems` and `funcProblems`, at any
depth (`docs/decisions/validation-fir-ref.md`, "`decide` on validity").
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

/-- `DialectItem.problems`, compiled after `allWritable_eq_writableLoop`. -/
def dialectItemProblems (ctx : FuncContext d) (i : DialectItem d) : List Problem :=
  (if isDialectWord i.kind then [] else
    [i.problem ("the kind " ++ Text.quote i.kind ++ " is not a word of a dialect")]) ++
  i.params.filterMap (fun x => if isName x.1 then none else
    some (i.problem ("the parameter " ++ valueRef x.1 ++ " is not a name"))) ++
  (repeats (i.params.map (·.1))).map (fun x =>
    i.problem ("the item defines " ++ valueRef x ++ " more than once")) ++
  (if ∀ t ∈ i.types, validTy t then [] else [i.problem "a type of the item is not valid"]) ++
  (if Attr.allWritable i.attrs then [] else
    [i.problem "an attribute of the item cannot be written"]) ++
  i.kindProblems ctx

@[csimp] theorem problems_eq_dialectItemProblems :
    @DialectItem.problems = @dialectItemProblems := rfl

/-- `SymbolTable.problems`, compiled after `problems_eq_funcProblems` and
`problems_eq_dialectItemProblems`. -/
def tableProblems (held : Std.HashSet LocRef) (t : SymbolTable d) : List Problem :=
  let lk := t.lookup held
  (repeats (t.items.map Item.name)).map (fun s =>
    { message := "the symbol " ++ Text.printSymbol s ++ " names more than one item", func := s }) ++
  t.funcs.flatMap (·.problems lk) ++
  t.dialectItems.flatMap (·.problems ⟨lk.symbols⟩) ++
  t.dialects.filterMap (fun x => if isWord x then none else
    some { message := "the dialect set names " ++ Text.quote x ++ ", which is not a word" }) ++
  (repeats t.dialects).map fun x => { message := "the dialect set names " ++ x ++ " more than once" }

@[csimp] theorem problems_eq_tableProblems : @SymbolTable.problems = @tableProblems := rfl

/-- `Func.types`, compiled after `allBlocks_eq_allBlocks`: the check of the
memories that a module's types name lists each function's types, and the
spec's code of `Func.types` calls the spec's walk. -/
def funcTypes (f : Func d) : List d.Ty :=
  f.results ++ (f.params ++ f.allBlocks.flatMap Block.defs).map (·.2)

@[csimp] theorem types_eq_funcTypes : @Func.types = @funcTypes := rfl

/-- `SymbolTable.memoryProblems`, compiled after `types_eq_funcTypes`. -/
def tableMemoryProblems (l : DataLayout) (t : SymbolTable d) : List Problem :=
  t.funcs.filterMap (fun f => memoryProblem f.name (l.missing f.types)) ++
  t.dialectItems.filterMap (fun i => memoryProblem i.name (l.missing i.types))

@[csimp] theorem memoryProblems_eq_tableMemoryProblems :
    @SymbolTable.memoryProblems = @tableMemoryProblems := rfl

/-- `Module.problems`, compiled after `problems_eq_tableProblems`,
`memoryProblems_eq_tableMemoryProblems` and `tables_eq_moduleTables`. -/
def moduleProblems (m : Module d) : List Problem :=
  let held := Std.HashSet.ofList (m.locs.map (·.1))
  m.locs.problems ++ m.tables.flatMap (·.problems held) ++ m.layout.problems ++
    m.tables.flatMap (·.memoryProblems m.layout)

@[csimp] theorem problems_eq_moduleProblems : @Module.problems = @moduleProblems := rfl

/-! # The dialect set

The check of a module's dialect set lists each function's blocks too, through
`Func.types` and `Func.allBlocks`, so it has copies here, compiled after
`allBlocks_eq_allBlocks`. `wordDialects` writes `Func.types` out, as the
spec's code of `Func.types` calls the spec's walk. The words of a type or of
an op's attribute are walked by recursion, once per level of an applied
attribute, but `fir-ref` decodes only the core dialect, whose ops and types
hold attributes of one level. The attributes of an item of a dialect's kind
are kept as the text writes them, at any depth, so `DialectItem.wordDialects`
has a copy compiled after `dialectsAll_eq_dialectsOf`.
-/

section

variable {d : Dialect} [DialectText d] [DialectSet d]

/-- `Func.wordDialects`, compiled after `allBlocks_eq_allBlocks`. -/
def wordDialects (f : Func d) : List String :=
  let all := f.allBlocks
  (f.results ++ (f.params ++ all.flatMap Block.defs).map (·.2)).flatMap (fun t => (tyAttr t).dialects) ++
    all.flatMap fun b => b.body.flatMap Operation.wordDialects

@[csimp] theorem wordDialects_eq_wordDialects : @Func.wordDialects = @wordDialects := rfl

/-- `Func.setProblems`, compiled after `wordDialects_eq_wordDialects`. -/
def funcSetProblems (ns : List Name) (f : Func d) : List Problem :=
  match f.wordDialects.find? (· ∉ ns) with
  | some x => [f.problem ("the function writes a word of the dialect " ++ x ++
      ", which the module's dialect set does not name")]
  | none => []

@[csimp] theorem setProblems_eq_funcSetProblems : @Func.setProblems = @funcSetProblems := rfl

/-- `DialectItem.wordDialects`, compiled after `dialectsAll_eq_dialectsOf`. -/
def itemWordDialects (i : DialectItem d) : List String :=
  (wordDialect i.kind).toList ++ i.types.flatMap (fun t => (tyAttr t).dialects) ++
    Attr.dialectsAll i.attrs

@[csimp] theorem wordDialects_eq_itemWordDialects :
    @DialectItem.wordDialects = @itemWordDialects := rfl

/-- `DialectItem.setProblems`, compiled after `wordDialects_eq_itemWordDialects`. -/
def itemSetProblems (ns : List Name) (i : DialectItem d) : List Problem :=
  match i.wordDialects.find? (· ∉ ns) with
  | some x => [{ message := "the item writes a word of the dialect " ++ x ++
      ", which the module's dialect set does not name", func := i.name }]
  | none => []

@[csimp] theorem setProblems_eq_itemSetProblems :
    @DialectItem.setProblems = @itemSetProblems := rfl

/-- `SymbolTable.setProblems`, compiled after `setProblems_eq_funcSetProblems`
and `setProblems_eq_itemSetProblems`. -/
def tableSetProblems (t : SymbolTable d) : List Problem :=
  t.dialects.filterMap (fun x => if x ∈ names d then none else
    some { message := "the dialect set names " ++ x ++ ", which is not a known dialect" }) ++
  t.funcs.flatMap (Func.setProblems t.dialects) ++
  t.dialectItems.flatMap (DialectItem.setProblems t.dialects)

@[csimp] theorem setProblems_eq_tableSetProblems :
    @SymbolTable.setProblems = @tableSetProblems := rfl

/-- `Module.setProblems`, compiled after `setProblems_eq_tableSetProblems`. -/
def moduleSetProblems (m : Module d) : List Problem := m.tables.flatMap SymbolTable.setProblems

@[csimp] theorem setProblems_eq_moduleSetProblems :
    @Module.setProblems = @moduleSetProblems := rfl

end

/-! # `decide` on validity -/

/-- `Decidable m.Valid`, compiled after `problems_eq_moduleProblems`: the
spec's instance, word for word, so its code calls `moduleProblems`. Its
priority puts it before the spec's wherever this module is imported. -/
instance (priority := high) decidableValid (m : Module d) : Decidable m.Valid :=
  decidable_of_iff _ m.problems_eq_nil_iff

/-- `Decidable (f.Valid ctx)`, compiled after `problems_eq_funcProblems`, as
`decidableValid` is. -/
instance (priority := high) decidableFuncValid (ctx : ModuleContext d) (f : Func d) :
    Decidable (f.Valid ctx) :=
  decidable_of_iff _ (Func.problems_eq_nil (lk := ⟨ctx.symbols, fun r => decide (r ∈ ctx.locKeys)⟩)
    ⟨rfl, by simp⟩)

/-- `decidableValid` is the spec's instance, so `decide` gives the same
answer with either. -/
theorem decidableValid_eq : @decidableValid = @Fir.instDecidableValid := rfl

/-- `decidableFuncValid` is the spec's instance, so `decide` gives the same
answer with either. -/
theorem decidableFuncValid_eq : @decidableFuncValid = @Fir.instDecidableValid_1 := rfl

end FirRef
