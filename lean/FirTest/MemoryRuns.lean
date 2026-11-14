import FirTest.Calls
import Fir.Core.MemoryCallRefine

/-!
Tests of runs with memory: the frame hook frees a call's stack allocations
when the call returns, and leaves every other allocation as it was
(ADR-2026-11-09-1548). No core op touches memory yet, so a semantics
written here for these tests, not fir's, gives `const` an allocation: it
allocates a unit of the given kind in the run's one memory, then gives its
constant by the core rule. The runs are those of the interpreter in the
state layer over the tree of choices, walked by exhaustive mode, from the
empty memories.
-/

namespace FirTest.MemoryRuns

open Fir Fir.Memory FirRef

/-- The memories of these runs: one memory, of 8-bit units. -/
abbrev Mems := Memories Unit (fun _ => 8)

/-- The state layer over the tree of choices that `fir-ref run` runs the
core dialect in. -/
abbrev MemTree := StateT Mems (ChoiceTree Core.Op)

/-- The tree of choices of `fir-ref run`. -/
abbrev Tree := ChoiceTree Core.Op

/-- A semantics, not fir's, in which `const` allocates one unit of kind `k`
before it gives its constant. Every other op keeps its core rule and the
memories. -/
@[instance_reducible] def constAllocates (k : AllocKind) : DialectDenote CoreDialect MemTree where
  denote
    | Core.Op.const w v, args => do
      let _ ← MonadMemory.alloc () k 1 1
      StateT.lift (DialectDenote.denote (m := Tree) (d := CoreDialect) (Core.Op.const w v) args)
    | op, args => StateT.lift (DialectDenote.denote (m := Tree) op args)
  exit op args := StateT.lift (DialectDenote.exit (m := Tree) op args)

/-- A semantics, not fir's, in which `const 3` loads a unit from the
allocation with id 1 and every other `const` allocates a unit on the stack,
before each gives its constant. -/
@[instance_reducible] def constThreeLoads : DialectDenote CoreDialect MemTree where
  denote
    | Core.Op.const w v, args => do
      if v.toNat = 3 then discard <| MonadMemory.load () ⟨some 1, 0⟩ 1
      else discard <| MonadMemory.alloc () .stack 1 1
      StateT.lift (DialectDenote.denote (m := Tree) (d := CoreDialect) (Core.Op.const w v) args)
    | op, args => StateT.lift (DialectDenote.denote (m := Tree) op args)
  exit op args := StateT.lift (DialectDenote.exit (m := Tree) op args)

/-- What a path of a run shows of its memories: the liveness of each
allocation of the one memory, in order, and the number of frames left. -/
def shown (S : Mems) : List Bool × Nat := ((S.mem ()).blocks.map (·.live), S.frames.length)

/-- Every way the run of the function `func` of the text `t` may end, with
the semantics `sem`, and what each path shows of its memories; a path that
ends in UB shows none. `none` when the text does not parse or a path
chooses. -/
def memRunWith (sem : DialectDenote CoreDialect MemTree) (t func : String) :
    Option (List (Bool × List Bool × Nat)) :=
  match parseCore t with
  | .error _ => none
  | .ok M => match M.funcs.find? (Text.printSymbol ·.name == func) with
    | none => none
    | some f => match readArgs (f.params.map (·.2)) [] with
      | .error _ => none
      | .ok args => letI := sem
        (ChoiceTree.explore ((f.run M (m := MemTree) args 1000).run Memories.empty) 0).map
          fun ls => ls.map fun
            | (.ok (.ok (.ret _), S), _) => (true, shown S)
            | (.ok (_, S), _) => (false, shown S)
            | _ => (false, [], 0)

/-- `memRunWith`, with `const` allocating on kind `k`. -/
def memRun (k : AllocKind) (t func : String) : Option (List (Bool × List Bool × Nat)) :=
  memRunWith (constAllocates k) t func

/-- `@inner` makes one constant; `@outer` makes one, then calls `@inner`,
then makes another. -/
def nested : String := withFuncs [
  "func @inner() -> i8 {\n^e:\n  %c: i8 = const 1 @0\n  ret %c @0\n}\n",
  "func @outer() -> i8 {\n^e:\n  %a: i8 = const 2 @0\n  %b: i8 = call @inner @0\n" ++
    "  %d: i8 = const 3 @0\n  ret %b @0\n}\n"]

-- A function's stack allocations are freed when it returns: `@inner`'s on
-- its return to `@outer`, and `@outer`'s when the run returns. No frame is
-- left.
#guard memRun .stack nested "@inner" == some [(true, [false], 0)]
#guard memRun .stack nested "@outer" == some [(true, [false, false, false], 0)]
-- An allocation of another kind is in no frame: it stays live.
#guard memRun .heap nested "@outer" == some [(true, [true, true, true], 0)]
#guard memRun .global nested "@inner" == some [(true, [true], 0)]
-- `@inner`'s allocation is freed on its return to `@outer`, before `@outer`
-- returns: `const 3` in `@outer` then loads from it, which is UB.
#guard memRunWith constThreeLoads nested "@outer" == some [(false, [], 0)]

/-! # Fuel monotonicity with memory

The runs with memory of every dialect are fuel-monotone, whatever its ops
do to the memories. `constAllocatesSet` is `constAllocates` in the state
layer over the set monad: the theorem on runs of ops covers it, so a run of
ops that allocates with more fuel is ahead of the run with less, from the
same memories. The alloc dialect's one op allocates by its semantics with
memory, and the theorem on runs with memory covers its runs. -/

/-- `constAllocates`, in the state layer over the set monad. -/
@[instance_reducible] def constAllocatesSet (k : AllocKind) :
    DialectDenote CoreDialect (StateT Mems SetM) where
  denote
    | Core.Op.const w v, args => do
      let _ ← MonadMemory.alloc () k 1 1
      StateT.lift (DialectDenote.denote (m := SetM) (d := CoreDialect) (Core.Op.const w v) args)
    | op, args => StateT.lift (DialectDenote.denote (m := SetM) op args)
  exit op args := StateT.lift (DialectDenote.exit (m := SetM) op args)

example (k : AllocKind) (M : Module CoreDialect) (f : Func CoreDialect) (env : Env CoreDialect)
    (os : List (Operation CoreDialect)) (n j : Nat) (S : Mems) :
    letI := constAllocatesSet k
    Ahead j (runFrom (Func.runOps (m := StateT Mems SetM) M n f env os) S)
      (runFrom (Func.runOps (m := StateT Mems SetM) M (n + j) f env os) S) :=
  letI := constAllocatesSet k
  Func.runOps_memAhead M n j f env os S

/-- The ops of the alloc dialect: `alloc` allocates one unit on the stack of
the dialect's one memory, and gives no result; `ret` returns nothing. -/
inductive AllocOp where
  | alloc
  | ret
  deriving DecidableEq

/-- A dialect, for these tests, whose op `alloc` touches memory: its
semantics with memory allocates, so it lifts no semantics in the set
monad. -/
abbrev AllocDialect : Dialect := ⟨AllocOp, Core.Ty⟩

instance : DialectSignature AllocDialect where
  sig _ := []
  returnTypes _ := []
  isTerminator
    | .alloc => false
    | .ret => true
  succCount _ := 0

instance : DialectCall AllocDialect := ⟨fun _ => none⟩

/-- The alloc dialect has one memory, `()`; `alloc` declares that it
allocates in it, and `ret` that it is a terminator. -/
instance : DialectEffects AllocDialect :=
  ⟨Unit, fun _ => .exception, fun
    | .alloc => { allocates := .these [()] }
    | .ret => { control := true }⟩

/-- Wherever a run names the memory `()` as `ρ ()`, `alloc` allocates one
unit on its stack, and `ret` returns. -/
instance : DialectMemDenote AllocDialect where
  denoteAt _ ρ :=
    { denote := fun
        | .alloc, _ => (fun _ => .nil) <$> MonadMemory.alloc (ρ ()) .stack 1 1
        | .ret, _ => MonadUB.ub "ret is a terminator"
      exit := fun
        | .alloc, _ => MonadUB.ub "alloc is not a terminator"
        | .ret, _ => pure .ret }

/-- A run with memory of the alloc dialect runs its semantics with memory at
the naming it is given. -/
example {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Unit → N) (M : Module AllocDialect)
    (f : Func AllocDialect) (args : HVector toType (f.params.map (·.2))) (n : Nat) :
    letI := DialectMemDenote.denoteAt (d := AllocDialect) lay ρ
    f.memRuns lay ρ M args n = Functor.map (f := SetM) Prod.fst
      ((f.run M (m := StateT (Memories N (unitsOf lay)) SetM) args n).run Memories.empty) :=
  rfl

/-- The runs with memory of the alloc dialect, whose op allocates, are
fuel-monotone. -/
example (M : Module AllocDialect) (f : Func AllocDialect)
    (args : HVector toType (f.params.map (·.2))) :
    FuelMonotone (f.memRuns (fun _ : Unit => MemLayout.default) id M args) :=
  Func.memRuns_fuelMonotone _ _ M f args

/-- info: 'Fir.Func.memRuns_fuelMonotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.memRuns_fuelMonotone

/-! # Progress with an op that allocates -/

/-- Validation of the alloc dialect accepts every type and function, and
`ret` in a function with no results. -/
instance : DialectValidation AllocDialect where
  validTy _ := True
  symbolRefs _ := []
  validOp ctx op := op = .ret → ctx.results = []
  validFunc _ _ _ := True

instance : DecidableDialectValidation AllocDialect where
  decValidTy _ := inferInstanceAs (Decidable True)
  decValidOp ctx op := inferInstanceAs (Decidable (op = .ret → ctx.results = []))
  decValidFunc _ _ _ := inferInstanceAs (Decidable True)

/-- Each alloc op has an outcome from any memories, wherever a run names
the dialect's memory: an allocation always succeeds, and `ret` returns. -/
theorem alloc_memTotal : ∀ op : AllocOp, MemTotal (d := AllocDialect) op
  | .alloc => fun _ _ _ => ⟨fun _ => HasOutcome.map _ fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩
  | .ret => fun _ _ _ => ⟨fun h => (nomatch h), fun _ _ => ⟨_, rfl⟩⟩

/-- The alloc dialect is lawful in its totality, with no semantics in the
set monad. -/
instance : LawfulDialectTotal AllocDialect := ⟨fun op _ _ => alloc_memTotal op⟩

/-- Every valid function of the alloc dialect runs within its module with
memory, at every naming: no op calls a function, `alloc` never exits, and
`ret` returns from a function with no results, by its validation rule. -/
theorem alloc_inModuleAt {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Unit → N)
    {ctx : ModuleContext AllocDialect} (M : Module AllocDialect) {f : Func AllocDialect}
    (hv : f.Valid ctx) : f.InModuleAt lay ρ M := by
  letI := DialectMemDenote.denoteAt (d := AllocDialect) lay ρ
  show f.MemInModule (unitsOf lay) M
  refine ⟨fun _ _ _ _ _ _ h => (nomatch h), fun _ _ o _ _ _ _ _ _ h => ?_,
    fun b hb o ho _ _ _ _ h => ?_⟩
  · cases o with | mk _ op _ _ _ _ => cases op <;> cases h
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
    have hvalid := (hv.ops b hb i b.body[i] (List.getElem?_eq_getElem hi)).2.2.2.2.2.2.2.2.2.1
    revert hvalid h
    cases b.body[i].op with
    | alloc => intro h; cases h
    | ret => intro _ hvalid; exact (hvalid rfl).symm

/-- A function of the alloc dialect that allocates, then returns. -/
def allocMain : Func AllocDialect where
  name := "main"
  params := []
  results := []
  body := { blocks := [{ label := "entry", params := [], body := [
    { results := [], op := .alloc, operands := [], succs := [], regions := [], loc := 0 },
    { results := [], op := .ret, operands := [], succs := [], regions := [], loc := 0 }] }] }

/-- A module of the alloc dialect with that one function. -/
def allocModule : Module AllocDialect := { items := [.func allocMain], locs := [(0, .unknown)] }

/-- `allocMain` is valid in its module. -/
theorem allocMain_valid : allocMain.Valid allocModule.context where
  bodyKind := rfl
  entry := ⟨_, rfl, rfl⟩
  reachable b hb := by
    simp only [allocMain, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    exact .entry rfl
  labelsUnique := by decide
  namesUnique := by decide +kernel
  names x hx := Text.isName_iff.2 (by revert x; decide +kernel)
  labels b hb := Text.isName_iff.2 (by revert b; decide +kernel)
  types t ht := by revert t; decide +kernel
  blocksNonEmpty b hb := by
    simp only [allocMain, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    simp
  ops b hb i o ho := by
    simp only [allocMain, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    match i, ho with
    | 0, ho =>
      cases ho
      exact ⟨Func.regionsValid_of_nil rfl rfl, rfl, rfl, by decide, rfl, fun _ => rfl,
        fun _ h => (nomatch h), fun _ h => (nomatch h), fun _ h => (nomatch h), fun h => (nomatch h),
        by decide⟩
    | 1, ho =>
      cases ho
      exact ⟨Func.regionsValid_of_nil rfl rfl, rfl, rfl, by decide, rfl, fun h => (nomatch h),
        fun _ h => (nomatch h), fun _ h => (nomatch h), fun _ h => (nomatch h), fun _ => rfl,
        by decide⟩
  inner := Func.inner_of_noRegions (by decide +kernel)
  dialect := trivial

/-- The module is valid. -/
theorem allocModule_valid : allocModule.Valid := Module.valid_of_flat
  (by decide)
  (by decide)
  (⟨by decide, by unfold LocTable.InLimits; decide +kernel, fun e he => by
    simp only [allocModule, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    simp [Location.WellFormed, Location.refs]⟩)
  (fun f hf => by
    simp only [allocModule, Module.funcs, List.filterMap_cons, Item.func?, List.filterMap_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    exact allocMain_valid)
  (by simp [allocModule])
  (by simp [allocModule])

/-- A run with memory of a valid module of the alloc dialect, whose op
allocates, is never stuck and has an outcome at every budget. -/
theorem allocModule_runsWell {f : Func AllocDialect} (hf : f ∈ allocModule.funcs)
    (args : HVector toType (f.params.map (·.2))) :
    NeverStuck (f.memRuns (fun _ : Unit => MemLayout.default) id allocModule args) ∧
      Progress (f.memRuns (fun _ : Unit => MemLayout.default) id allocModule args) :=
  have hv := allocModule_valid.funcs
  have hm := fun g hg => alloc_inModuleAt (fun _ : Unit => MemLayout.default) id allocModule (hv g
      hg)
  ⟨Func.memNeverStuck _ _ hv hm hf args, Func.memProgress _ _ hv hm hf args⟩

/-- `allocMain` is a function of the module, so the theorem holds of it. -/
example : allocMain ∈ allocModule.funcs := by simp [allocModule, Module.funcs]

/-- info: 'Fir.Func.memNeverStuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.memNeverStuck

/-- info: 'Fir.Func.memProgress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.memProgress

/-! # A run that touches no memory

Every core op but `alloca` touches no memory: a core function that reaches
no `alloca` reaches no memory, so it returns from given memories what it
returns with memory, with the memories it started from (the section on runs
that touch no memory). -/

example (M : Module CoreDialect) {s : Name} {f : Func CoreDialect} (hf : M.func? s = some f)
    (hno : ∀ g ∈ M.funcs, ∀ o ∈ g.allOps, o.op.touchesMemory = false)
    (args : HVector toType (f.params.map (·.2)))
    (S S' : Memories Unit (unitsOf fun _ : Unit => MemLayout.default)) (n : Nat)
    (vs : List (DVal CoreDialect)) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) (fun _ : Unit => MemLayout.default)
      fun _ => ()
    (f.memRunsFrom M (args, S) n).outcomes (.ret (vs, S')) ↔
      S' = S ∧ (f.memRuns (fun _ : Unit => MemLayout.default) (fun _ => ()) M args n).outcomes
        (.ret vs) :=
  Func.memRunsFrom_ret_iff _ _ (Core.opsIgnoreMemory _ _) hf (Core.reachesNoMemory_of_all s hno)
    args S n

end FirTest.MemoryRuns
