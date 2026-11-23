import FirTest.OverCore

/-!
A test-only dialect whose op picks its callee when it runs (#235, stage 1).
No core op does yet, so this dialect is where the interpreter's case for a
picked callee runs and is proved.

It extends the core dialect at the core's integers. `%r: iN = toy.pcall
[@f, @g, …] %t, %x` calls the function or external declaration that the
value of `%t` selects in its table, on `%x`: the rule of the op picks the
symbol, and the run calls it as it calls a direct one. The rule is UB when
`%t` is poison, when `%t` selects no entry of the table, and when the run
cannot call the selected symbol on an `iN` for an `iN`: no function or
declaration of that name and those types. `toy.const`, `toy.inc` and
`toy.ret` give a constant, add one, and return.

The runs below are in the tree of choices, whose external call is UB. The
proofs show that the dialect is lawful, its rule that picks included, so
that the generic theorems over runs apply to it: refined arguments, for
every function of every valid module.
-/

namespace FirTest.Pick

/-- An op instance of the picking dialect, at `iN` with `N = w`. -/
inductive Op where
  | const (w : Nat) (k : BitVec w)
  | inc (w : Nat)
  | pcall (w : Nat) (table : List Fir.Name)
  | ret (w : Nat)
  deriving DecidableEq

end FirTest.Pick

namespace FirTest

open Fir

/-- The picking dialect: its ops, over the core dialect's types. -/
abbrev PickDialect : Dialect := OverCore Pick.Op

namespace Pick

/-- The type `iN` of the core, as a type of the picking dialect. -/
abbrev int (w : Nat) : Core.Ty ⊕ Empty := .inl (.int w)

/-- The operand types of a picking op: the selector comes first. -/
def Op.sig : Op → List (Core.Ty ⊕ Empty)
  | .const .. => []
  | .inc w => [int w]
  | .pcall w _ => [int w, int w]
  | .ret w => [int w]

/-- The result types of a picking op. -/
def Op.returnTypes : Op → List (Core.Ty ⊕ Empty)
  | .const w _ | .inc w | .pcall w _ => [int w]
  | .ret _ => []

instance : DialectSignature PickDialect where
  sig := Op.sig
  returnTypes := Op.returnTypes
  isTerminator
    | .ret _ => true
    | _ => false
  succCount _ := 0

/-- `toy.pcall` picks its callee when it runs; no other op calls. -/
instance : DialectCall PickDialect := ⟨fun
  | .pcall .. => some .picked
  | _ => none⟩

/-- The symbol that the selector `t` picks in `table`, among those the run
can call (`ok`), or UB. -/
def pickIn {m : Type → Type} [Monad m] [MonadUB m] {w : Nat} (table : List Name)
    (ok : Name → Bool) : PoisonOr (BitVec w) → m Name
  | .poison => MonadUB.ub "the selector is poison"
  | .value t => match table[t.toNat]? with
    | none => MonadUB.ub "the selector picks no entry of the table"
    | some s => if ok s then pure s else MonadUB.ub "the run cannot call the entry it picks"

/-- `toy.inc`: one more, and poison of poison. -/
def incValue (w : Nat) : PoisonOr (BitVec w) → PoisonOr (BitVec w)
  | .value x => .value (x + 1)
  | .poison => .poison

/-- The rule of each picking op, in any monad with UB. -/
def Op.denote {m : Type → Type} [Monad m] [MonadUB m] : (op : Op) →
    HVector toType (Fir.sig (d := PickDialect) op) →
    m (HVector toType (Fir.returnTypes (d := PickDialect) op))
  | .const _ k, .nil => pure (.cons (.value k) .nil)
  | .inc w, .cons a .nil => pure (.cons (incValue w a) .nil)
  | .pcall .., _ => MonadUB.ub "a call runs its callee"
  | .ret _, _ => MonadUB.ub "a terminator exits"

/-- The exit of each picking op: `toy.ret` returns. -/
def Op.exit {m : Type → Type} [Monad m] [MonadUB m] : (op : Op) →
    HVector toType (Fir.sig (d := PickDialect) op) → m Exit
  | .ret _, _ => pure .ret
  | _, _ => MonadUB.ub "not a terminator"

/-- The rule of each picking op that picks its callee. -/
def Op.pick {m : Type → Type} [Monad m] [MonadUB m] : (op : Op) → (Name → Bool) →
    HVector toType (Fir.sig (d := PickDialect) op) → m Name
  | .pcall _ table, ok, .cons t _ => pickIn table ok t
  | _, _, _ => MonadUB.ub "the op picks no callee"

instance {m : Type → Type} [Monad m] [MonadUB m] : DialectDenote PickDialect m where
  denote := Op.denote
  exit := Op.exit
  pick := Op.pick

/-- In the tree of choices, which has no world, an external call is UB. -/
instance : DialectExtCall PickDialect (ChoiceTree Empty) := ⟨fun _ _ _ => MonadUB.ub extCallUB⟩

/-- Every op is valid at a valid type; a function takes any parameters. -/
instance : DialectValidation PickDialect where
  validTy := OverCore.ValidTy
  symbolRefs _ := []
  validOp _ _ := True
  validFunc _ _ _ := True

instance : DecidableDialectValidation PickDialect where
  decValidTy t := inferInstanceAs (Decidable (OverCore.ValidTy t))
  decValidOp _ _ := inferInstanceAs (Decidable True)
  decValidFunc _ _ _ := inferInstanceAs (Decidable True)

/-- The picking ops declare no poison propagation, may be UB, and touch no
memory of their own: their memories are the core's. -/
instance : DialectEffects PickDialect :=
  ⟨DialectEffects.Mem CoreDialect ⊕ Empty, fun _ => .exception, fun _ => { mayUB := true },
    fun _ => none⟩

/-! # Runs -/

/-- An op of the picking dialect with no regions, at location `0`. -/
def mk (results : List (Name × (Core.Ty ⊕ Empty))) (o : Op) (operands : List Name) :
    Operation PickDialect :=
  { results, op := o, operands, succs := [], regions := [], loc := 0 }

/-- A function of one `i8` parameter `%x` and one result, of the ops `ops`. -/
def fn (name : Name) (ops : List (Operation PickDialect)) : Func PickDialect where
  name := name
  params := [("x", int 8)]
  results := [int 8]
  body := { blocks := [⟨"entry", [], ops⟩] }

/-- `@f` returns `%x + 1`. -/
def f : Func PickDialect :=
  fn "f" [mk [("y", int 8)] (.inc 8) ["x"], mk [] (.ret 8) ["y"]]

/-- `@g` returns `%x`. -/
def g : Func PickDialect := fn "g" [mk [] (.ret 8) ["x"]]

/-- `@h` takes two parameters, so a call on one cannot pick it. -/
def h : Func PickDialect :=
  { fn "h" [mk [] (.ret 8) ["x"]] with params := [("x", int 8), ("y", int 8)] }

/-- `@ext`, an external declaration from `i8` to `i8`. -/
def ext : Extern PickDialect := { name := "ext", params := [("a", int 8)], results := [int 8] }

/-- `@main` calls the entry that the selector `%t`, of value `t`, picks in
`[@f, @g, @h, @nope, @ext]`, on `%x`. -/
def main (t : BitVec 8) : Func PickDialect :=
  fn "main" [
    mk [("t", int 8)] (.const 8 t) [],
    mk [("r", int 8)] (.pcall 8 ["f", "g", "h", "nope", "ext"]) ["t", "x"],
    mk [] (.ret 8) ["r"]]

/-- The module of the functions and the declaration, with `@main` at the
selector `t`. -/
def pickModule (t : BitVec 8) : Module PickDialect :=
  { items := [.func f, .func g, .func h, .extern ext, .func (main t)], locs := [(0, .unknown)] }

/-- How a run in the tree of choices ends, for the checks below: the value
it returns, UB, out of fuel, or stuck. -/
def outcome (t : ExceptT Stuck (ChoiceTree Empty) (Result (List (DVal PickDialect)))) : String :=
  match t.run with
  | .pure (.ok (.ret [⟨.inl (.int 8), .value v⟩])) => s!"ret {v.toNat}"
  | .pure (.ok (.ret _)) => "ret other"
  | .pure (.ok .fuelExhausted) => "fuel"
  | .pure (.error _) => "stuck"
  | .ub _ => "ub"
  | _ => "other"

/-- The run of `@main` at the selector `t`, on `%x = 5`, with `fuel` steps. -/
def runMain (t : BitVec 8) (fuel : Nat) : String :=
  outcome (Func.run (m := ChoiceTree Empty) (pickModule t) (main t)
    (.cons (.value 5) .nil) fuel)

-- The selector picks `@f`, which returns `6`, and `@g`, which returns `5`.
#guard runMain 0 10 == "ret 6"
#guard runMain 1 10 == "ret 5"
-- `@h` takes two parameters, so the run cannot call it on one: UB.
#guard runMain 2 10 == "ub"
-- `@nope` names nothing: UB.
#guard runMain 3 10 == "ub"
-- `@ext` is a declaration, which the external-call rule runs: UB without a world.
#guard runMain 4 10 == "ub"
-- A selector past the table: UB.
#guard runMain 9 10 == "ub"
-- The constant, the pick, the call, and `@f`'s two ops and the return take six steps.
#guard runMain 0 6 == "ret 6"
#guard runMain 0 5 == "fuel"
-- With one step after the constant, the rule picks and no step is left for the call.
#guard runMain 1 2 == "fuel"

/-! # The picking dialect is lawful -/

/-- The rule that picks has an outcome on every operand vector. -/
theorem pcall_pickTotal (w : Nat) (table : List Name) :
    PickTotal (d := PickDialect) (.pcall w table) := by
  intro ok args
  match args with
  | .cons t (.cons _ .nil) =>
    show ∃ e, pickIn (m := SetM) table ok t e
    cases t with
    | poison => exact ⟨_, rfl⟩
    | value v =>
      cases hs : table[v.toNat]? with
      | none => simp only [pickIn, hs]; exact ⟨_, rfl⟩
      | some s =>
        simp only [pickIn, hs]
        split
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩

/-- The rule that picks is monotone: a poison selector is UB, and a defined
one picks the same entry, which a run that can call more can call too. -/
theorem pcall_pickMonotone (w : Nat) (table : List Name) :
    PickMonotone (d := PickDialect) (.pcall w table) := by
  intro ok ok' hok args args' hr
  match args, args', hr with
  | .cons t (.cons _ .nil), .cons t' (.cons _ .nil), hr =>
    have ht := hr.1
    show SetM.IsRefinedBy Eq (pickIn table ok t) (pickIn table ok' t')
    intro e' he'
    cases t with
    | poison => exact ⟨_, rfl, trivial⟩
    | value v =>
      cases t' with
      | poison => exact ht.elim
      | value v' =>
        cases ht
        cases hs : table[v.toNat]? with
        | none => simp only [pickIn, hs]; exact ⟨_, rfl, trivial⟩
        | some s =>
          simp only [pickIn, hs] at he' ⊢
          by_cases h₁ : ok s = true
          · simp only [hok s h₁, h₁, ↓reduceIte] at he' ⊢
            exact ⟨e', he', by cases he'; exact rfl⟩
          · simp only [h₁, Bool.false_eq_true, ↓reduceIte]
            exact ⟨_, rfl, trivial⟩

/-- `incValue` keeps refinement. -/
theorem incValue_mono {w : Nat} {a a' : PoisonOr (BitVec w)} (h : PoisonOr.IsRefinedBy a a') :
    PoisonOr.IsRefinedBy (incValue w a) (incValue w a') := by
  cases a <;> cases a' <;> simp_all [incValue, PoisonOr.IsRefinedBy]

/-- `toy.inc` is monotone: it maps poison to poison and keeps a value. -/
theorem inc_monotone (w : Nat) : OpMonotone (d := PickDialect) (.inc w) := by
  intro args args' hr
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', hr with
  | .cons a .nil, .cons a' .nil, hr =>
    intro e he
    subst he
    exact ⟨_, rfl, incValue_mono hr.1, trivial⟩

/-- `toy.const` is monotone: it gives the same value. -/
theorem const_monotone (w : Nat) (k : BitVec w) : OpMonotone (d := PickDialect) (.const w k) := by
  intro args args' _
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args' with
  | .nil, .nil =>
    intro e he
    subst he
    exact ⟨_, rfl, (show PoisonOr.IsRefinedBy (PoisonOr.value k) (.value k) by
      simp [PoisonOr.IsRefinedBy]), trivial⟩

/-- `toy.ret` is monotone: it returns. -/
theorem ret_monotone (w : Nat) : OpMonotone (d := PickDialect) (.ret w) := by
  intro args args' _
  refine ⟨(fun h => nomatch h), fun _ e he => ?_⟩
  subst he
  exact ⟨_, rfl, rfl⟩

/-- The picking dialect is lawful: its ops are total and monotone, and its
rule that picks a callee picks totally and monotonically. -/
instance lawful : LawfulDialectPoison PickDialect where
  poison_isRefinedBy {t} := match t with
    | .inl _ => fun _ => Core.Ty.poison_isRefinedBy
    | .inr t => t.elim
  propagates _ _ h := nomatch h
  returnsOnDefined _ _ h := nomatch h
  total
    | .const .., _, _ => fun | .nil => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩
    | .inc _, _, _ => fun | .cons _ .nil => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩
    | .ret _, _, _ => fun _ => ⟨(fun h => nomatch h), fun _ => ⟨_, rfl⟩⟩
    | .pcall .., _, h => by cases h <;> simp_all
  monotone
    | .const w k, _, _ => const_monotone w k
    | .inc w, _, _ => inc_monotone w
    | .ret w, _, _ => ret_monotone w
    | .pcall .., _, h => by cases h <;> simp_all
  pickTotal
    | .pcall w table, _, _ => pcall_pickTotal w table
  pickMonotone
    | .pcall w table, _, _ => pcall_pickMonotone w table

instance : HRefinement (DVal PickDialect) (DVal PickDialect) := instHRefinementDVal

open SetM in
/-- Refined arguments for every function of every valid module of the picking
dialect: its runs on arguments that refine others refine its runs on those
others, calls through `toy.pcall` included. -/
theorem runs_args_isRefinedBy {M : Module PickDialect} {ctx : ModuleContext PickDialect}
    (hv : ∀ g ∈ M.funcs, g.Valid ctx) {fn : Func PickDialect} (hf : fn ∈ M.funcs)
    {a a' : HVector toType (fn.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a') :
    observable (fn.runs M a) ⊑ observable (fn.runs M a') :=
  Func.runs_args_isRefinedBy_of_lawful hv hf ha

/-- info: 'FirTest.Pick.runs_args_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms runs_args_isRefinedBy

/-- Progress for every function of every valid module of the picking dialect
whose functions run within it: a run has an outcome at every budget, the
rule that picks and the call it makes included. -/
theorem progress {M : Module PickDialect} {ctx : ModuleContext PickDialect}
    (hv : ∀ g ∈ M.funcs, g.Valid ctx) (hm : ∀ g ∈ M.funcs, g.InModule M) {fn : Func PickDialect}
    (hf : fn ∈ M.funcs) (args : HVector toType (fn.params.map (·.2))) : Progress (fn.runs M args) :=
  Func.progress_of_lawful hv hm hf args

/-- info: 'FirTest.Pick.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progress

end Pick

end FirTest
