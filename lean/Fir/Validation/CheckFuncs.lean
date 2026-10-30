import Fir.Validation.CheckOps

/-!
The check of a function follows `Func.Valid`, rule by rule, in its order.
It walks the function's blocks at any depth once, with `Func.allBlocks`, and
gives that list to `Func.problemsIn`, which looks at no other nested part of
the function. So a tool that has its own way to list the blocks, such as one
that takes no stack per level of nesting, runs the same check with it.
-/

namespace Fir

variable {d : Dialect}

/-- A problem about the function `f`. -/
def Func.problem (f : Func d) (message : String) : Problem := { message, func := f.name }

/-- A problem about the block `b` of the function `f`, at the location of
its first op. -/
def Func.blockProblem (f : Func d) (b : Block d) (message : String) : Problem :=
  { message, func := f.name, block := b.label, loc := b.body.head?.map (·.loc) }

/-- The problems of a function's entry block. -/
def Func.entryProblems (f : Func d) : List Problem :=
  match f.blocks with
  | [] => [f.problem "the function has no entry block"]
  | e :: _ =>
    if e.params.isEmpty then []
    else [f.blockProblem e ("the entry block " ++ labelRef e.label ++ " declares arguments: " ++
      "its arguments are the function's parameters")]

theorem Func.entryProblems_eq_nil (f : Func d) :
    f.entryProblems = [] ↔ ∃ e, f.blocks.head? = some e ∧ e.params = [] := by
  unfold Func.entryProblems
  split <;> simp_all

variable [DialectSignature d] [DialectValidation d] [DecidableEq d.Ty]
  [DecidableDialectValidation d]

/-- The problems of a function, given `all`, its blocks at any depth. -/
def Func.problemsIn (lk : Lookup d) (f : Func d) (all : List (Block d)) : List Problem :=
  let t := f.tables all
  let defs := f.params ++ all.flatMap Block.defs
  let reached := reachedIn t.graph t.start
  f.entryProblems ++
  f.blocks.filterMap (fun b => if reached.contains b.label then none else
    some (f.blockProblem b ("block " ++ labelRef b.label ++ " is not reachable from the entry"))) ++
  (repeats (f.blocks.map (·.label))).map (fun l =>
    { message := "label " ++ labelRef l ++ " names more than one block", func := f.name,
      block := l }) ++
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
  f.blocks.flatMap (fun b => b.body.zipIdx.flatMap fun (o, i) => opProblems lk f t b i o)

/-- The problems of a function, in the context of its module. -/
def Func.problems (lk : Lookup d) (f : Func d) : List Problem :=
  f.problemsIn lk f.allBlocks

omit [DecidableEq d.Ty] [DecidableDialectValidation d] in
theorem Func.valid_iff (ctx : ModuleContext d) (f : Func d) : f.Valid ctx ↔
    (∃ e, f.blocks.head? = some e ∧ e.params = []) ∧
    (∀ b ∈ f.blocks, f.Reachable b.label) ∧
    (f.blocks.map (·.label)).Nodup ∧
    (f.defs.map (·.1)).Nodup ∧
    (∀ x ∈ f.defs, isName x.1) ∧
    (∀ b ∈ f.allBlocks, isName b.label) ∧
    (∀ t ∈ f.types, validTy t) ∧
    (∀ b ∈ f.blocks, b.body ≠ []) ∧
    (∀ b ∈ f.blocks, ∀ (i : Nat) (o : Operation d), b.body[i]? = some o → f.OpValid ctx b i o) :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
    fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩⟩

omit [DialectSignature d] [DialectValidation d] [DecidableEq d.Ty]
  [DecidableDialectValidation d] in
theorem Func.reached_all (f : Func d) :
    (∀ b ∈ f.blocks,
      (reachedIn (f.tables f.allBlocks).graph (f.tables f.allBlocks).start).contains b.label = true) ↔
      ∀ b ∈ f.blocks, f.Reachable b.label :=
  forall_congr' fun b => imp_congr_right fun hb => Func.reachedIn_iff ⟨b, hb, rfl⟩

theorem Func.ops_all {lk : Lookup d} {ctx : ModuleContext d} (f : Func d) (h : lk.Agrees ctx) :
    (∀ b ∈ f.blocks, ∀ p ∈ b.body.zipIdx, opProblems lk f (f.tables f.allBlocks) b p.2 p.1 = []) ↔
      ∀ b ∈ f.blocks, ∀ (i : Nat) (o : Operation d), b.body[i]? = some o → f.OpValid ctx b i o := by
  refine forall_congr' fun b => imp_congr_right fun hb => ?_
  constructor
  · intro hp i o ho
    exact (opProblems_eq_nil h hb).mp (hp (o, i) (List.mem_zipIdx_iff_getElem?.mpr ho))
  · intro hv p hp
    exact (opProblems_eq_nil h hb).mpr (hv p.2 p.1 (List.mem_zipIdx_iff_getElem?.mp hp))

omit [DialectSignature d] [DecidableEq d.Ty] [DecidableDialectValidation d] in
theorem Func.types_all (f : Func d) :
    (∀ t ∈ f.types, validTy t) ↔ (∀ t ∈ f.results, validTy t) ∧ ∀ x ∈ f.defs, validTy x.2 := by
  constructor
  · intro h
    exact ⟨fun t ht => h t (List.mem_append_left _ ht),
      fun x hx => h x.2 (List.mem_append_right _ (List.mem_map_of_mem hx))⟩
  · rintro ⟨h₁, h₂⟩ t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact h₁ t ht
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
      exact h₂ x hx

/-- The check of a function decides `Func.Valid`. -/
theorem Func.problems_eq_nil {lk : Lookup d} {ctx : ModuleContext d} {f : Func d}
    (h : lk.Agrees ctx) : f.problems lk = [] ↔ f.Valid ctx := by
  rw [Func.valid_iff, ← Func.reached_all, ← f.ops_all h, Func.types_all]
  simp only [Func.problems, Func.problemsIn, List.append_eq_nil_iff, Func.entryProblems_eq_nil,
    List.filterMap_eq_nil_iff, ite_none_eq_none, List.map_eq_nil_iff, repeats_eq_nil,
    List.flatMap_eq_nil_iff, Func.defs, List.mem_append, or_imp, forall_and, Prod.forall,
    and_assoc]

end Fir
