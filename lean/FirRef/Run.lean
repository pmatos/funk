import Std.Data.HashSet
import Fir
import FirRef.Utf8
import FirRef.Report
import FirRef.Sample
import FirRef.RunModes
import FirRef.RunText

/-!
What `fir-ref run` does with a file: it parses it with the dialects in tree,
the core and `gpu`, runs one of its functions, or a kernel of one of its
nested modules, as one work-item (`Gpu.WorkItem`) with the spec's
interpreter, `Func.run`, and reports the result as one JSON object on one
line (`docs/decisions/fir-ref-command-line.md#fir-ref-run`).

`freeze` of poison makes a choice, so a run may end in many ways.
`fir-ref` runs the interpreter in the state layer over the spec's tree of
choices, from the empty memories, with the rules of the core and `gpu`, and
walks the tree in one of three modes, the spec's `Gpu.scripted`,
`Gpu.exhaustive` and `Gpu.sampled`, which Lean proves sound for the runs
with memory (`Gpu.scripted_memOutcomes`, `Gpu.exhaustive_memOutcomes` and
`Gpu.sampled_memOutcomes`):

* scripted mode, the default, follows the one path that a choice sequence
  names, given with `--choices`, and reports its one outcome. With no
  `--choices`, the sequence is empty, so a run that makes no choice
  reports its one outcome, with a count of `0` choices, and one that makes
  a choice is an error;
* exhaustive mode, `--exhaustive`, reports every outcome of the run, when
  no path chooses more bits in all than its budget, `--choice-bits`;
* sampled mode, `--seed`, follows the path on which a generator seeded
  with its number draws each choice, the spec's `Gpu.sampled`, and
  reports its one outcome and the values it drew, a sequence that
  `--choices` takes (`Gpu.sampled_fits`).

Each says how many choices a path made. An op without rules has no outcome in
the spec, so a path that reaches one is reported as an error, not as a result
(`docs/decisions/fir-ref.md#an-op-without-rules`), and so is a choice sequence
that does not fit the run.

Arguments, choices and values are spelled as constants are in text: `true`
and `false` at `i1`, signed decimal at every other width, and the one
float literal of a float's bits at a float type (ADR-2026-11-11-1438), read
with the spec's lexer and checked with `Core.Op.decode`. `fir-ref` runs the spec's
lexer here as `argAttrP`, which lexes at most two tokens over the text's
positions, with no stack per character (`argAttr_eq_argAttrP`). A value or
an argument may also be `poison`, at any `iN` or float type, so that a run may start from
poison, as the runs of `Core.FuncRuns` do (#123). A choice may not:
`freeze` chooses a value of its type.
-/

namespace FirRef

open Fir

/-- A type as text writes it, such as `i8`. -/
def tyText (t : Core.Ty) : String := t.attr.print

/-- An op as text writes its name and attributes, such as `add nsw`. -/
def opText (op : Core.Op) : String := " ".intercalate (op.name :: op.attrs.map Attr.print)

/-- A value as `fir-ref run` spells it: as a constant of its type in text,
or `poison`. A float is written as the one float literal of its bits
(ADR-2026-11-11-1438). A pointer is written `ptr(A, O)`, for the
allocation `A` it has provenance for and its offset `O`, and
`ptr(none, O)` when it has no provenance. It names no address, which a
pointer has only once it is exposed (ADR-2026-11-09-1542). So the
pointer that the first `alloca` of a run in a memory gives is
`ptr(0, 0)` (#231). -/
def valueText : DVal CoreDialect → String
  | ⟨.int w, v⟩ => match (v : PoisonOr (BitVec w)) with
    | .poison => "poison"
    | .value b => (Core.constAttr w b).print
  | ⟨.float e m, v⟩ => match (v : PoisonOr (BitVec (Core.floatWidth e m))) with
    | .poison => "poison"
    | .value b => (Attr.float (Core.floatLit e m b)).print
  | ⟨.ptr _, v⟩ => match (v : PoisonOr Memory.Pointer) with
    | .poison => "poison"
    | .value p =>
      let a := match p.prov with | some a => toString a | none => "none"
      s!"ptr({a}, {(Attr.int p.offset).print})"

/-- The values that `fir-ref run` reports, spelled as `valueText` spells
them: the core's, and those of the sum of the core and `gpu`, whose types
are the core's. -/
class RunValue (V : Type) where
  text : V → String

instance : RunValue (DVal CoreDialect) := ⟨valueText⟩

instance : RunValue (DVal CoreGpu) where
  text
    | ⟨.inl t, v⟩ => valueText ⟨t, v⟩
    | ⟨.inr e, _⟩ => e.elim

/-- The `const` op that the text `s` spells at the type `t`: the spec's
lexer reads `s` as one token (`argAttr`, which `fir-ref` runs as
`argAttrP`, over positions), `Core.Op.decode` reads that as a `const`, and
the token is spelled exactly `s`, with nothing around it. -/
def constOpOf (t : Core.Ty) (s : String) : Option Core.Op := do
  let attr ← argAttr s
  if attr.print != s then none
  Core.Op.decode "const" [attr] [] [t]

/-- The constant that the text `s` spells at the type `iN` (`constOpOf`). -/
def constOf (w : Nat) (s : String) : Option (BitVec w) :=
  match constOpOf (.int w) s with
  | some (.const w' v) => if h : w' = w then some (h ▸ v) else none
  | _ => none

/-- The constant that the text `s` spells at the float type `float<e,m>`
(`constOpOf`): the one float literal of its bits. -/
def floatConstOf (e m : Nat) (s : String) : Option (BitVec (Core.floatWidth e m)) :=
  match constOpOf (.float e m) s with
  | some (.fconst e' m' v) => if h : e' = e ∧ m' = m then some (h.1 ▸ h.2 ▸ v) else none
  | _ => none

/-- An argument of type `t`: a constant of `t`, or `poison` at any `iN` and
any float type, spelled as `valueText` spells it. A pointer argument is
`poison`: a run starts with no allocation, so no pointer has provenance
for one. So a pointer that `valueText` writes, `ptr(A, O)`, is the one
value of the output that is no argument. -/
def readArg : (t : Core.Ty) → String → Except String ⟦t⟧
  | .int w, "poison" => pure (.poison : PoisonOr (BitVec w))
  | .int w, s => match constOf w s with
    | some v => pure (.value v : PoisonOr (BitVec w))
    | none => .error s!"{shown s} is not a value of type {tyText (.int w)}"
  | .float e m, "poison" => pure (.poison : PoisonOr (BitVec (Core.floatWidth e m)))
  | .float e m, s => match floatConstOf e m s with
    | some v => pure (.value v : PoisonOr (BitVec (Core.floatWidth e m)))
    | none => .error s!"{shown s} is not a value of type {tyText (.float e m)}"
  | .ptr _, "poison" => pure (.poison : PoisonOr Memory.Pointer)
  | .ptr n, s => .error s!"{shown s} is not a value of type {tyText (.ptr n)}"

/-- One argument for each type of `ts`. -/
def readArgs : (ts : List Core.Ty) → List String → Except String (HVector toType ts)
  | [], [] => pure .nil
  | t :: ts, a :: as => return .cons (← readArg t a) (← readArgs ts as)
  | ts, as => .error s!"{as.length} arguments are given for {ts.length} parameters"

/-- One argument for each type of `ts`, types of the sum of the core and
`gpu`, which are the core's. -/
def readGpuArgs : (ts : List CoreGpu.Ty) → List String → Except String (HVector toType ts)
  | [], [] => pure .nil
  | .inl t :: ts, a :: as => return .cons (← readArg t a) (← readGpuArgs ts as)
  | .inr e :: _, _ :: _ => e.elim
  | ts, as => .error s!"{as.length} arguments are given for {ts.length} parameters"

/-- The JSON object that reports a result of `kind`, with more fields. Its
strings are escaped as `fir-ref validate`'s are. -/
def resultJson (kind : String) (more : List (String × String) := []) : String :=
  jsonObject (("kind", jsonString kind) :: more)

/-- A leaf of a run's tree, as `fir-ref run` sees it, with the values of
type `V` that a path returns. -/
abbrev RunLeaf (V : Type := DVal CoreDialect) :=
  ChoiceTree.Leaf Core.Op (Except Stuck (Result (List V)))

variable {V : Type} [RunValue V]

/-- The fields of the JSON object that reports how a path ends, other than
the choices it made, and whether it is stuck; or the op without rules that
the path reaches. -/
def pathFields : PathEnd (List V) Core.Op → Except Core.Op (List (String × String) × Bool)
  | .outcome (.ret vs) =>
    .ok ([("kind", jsonString "return"),
      ("values", jsonArray (vs.map (jsonString ∘ RunValue.text)))],
      false)
  | .outcome .fuelExhausted => .ok ([("kind", jsonString "fuel-exhausted")], false)
  | .outcome (.ub r) => .ok ([("kind", jsonString "ub"), ("reason", jsonString r)], false)
  | .stuck st => .ok ([("kind", jsonString "stuck"), ("reason", jsonString st.reason)], true)
  | .noOutcome op => .error op

/-- The error of a run that reaches an op without rules
(`docs/decisions/fir-ref.md#an-op-without-rules`). -/
def noRules (name : String) (op : Core.Op) : RunReport :=
  { err := s!"fir-ref: {name}: {opText op} has no execution rules yet", status := 2 }

/-- Why a choice sequence does not fit the run, in words. -/
def misfitText : ChoiceTree.Misfit String → String
  | .short made w =>
    s!"the run makes choice {made + 1}, of type {tyText (.int w)}, and --choices gives " ++
      count made "choice"
  | .unread made w s => s!"choice {made + 1}, {shown s}, is not a value of type {tyText (.int w)}"
  | .long made n => s!"the run makes {count made "choice"}, and --choices gives {n}"

/-- The report of scripted mode on a run of the function whose symbol is
written `name`: the one path that the choices name, or why they do not fit
the run. -/
def scriptedReport (name : String) :
    Except (ChoiceTree.Misfit String) (RunLeaf V × Nat) → RunReport
  | .error m => { err := s!"fir-ref: {name}: the choices do not fit the run: {misfitText m}",
                  status := 2 }
  | .ok (l, c) => match pathFields (V := V) l.pathEnd with
    | .error op => noRules name op
    | .ok (fields, stuck) =>
      { out := jsonObject (fields ++ [("choices", toString c)]), status := if stuck then 1 else 0 }

/-- A value that a path chose, spelled as `--choices` takes it: as a
constant of its type. -/
def chosenText : ChoiceTree.Chosen → String
  | ⟨w, b⟩ => (Core.constAttr w b).print

/-- The report of sampled mode on a run of the function whose symbol is
written `name`: the one path that the generator draws, and the values it
drew on it. -/
def sampledReport (name : String) : RunLeaf V × List ChoiceTree.Chosen → RunReport
  | (l, cs) => match pathFields (V := V) l.pathEnd with
    | .error op => noRules name op
    | .ok (fields, stuck) =>
      { out := jsonObject (fields ++ [("choices", toString cs.length),
          ("sequence", jsonArray (cs.map (jsonString ∘ chosenText)))]),
        status := if stuck then 1 else 0 }

/-- The report of exhaustive mode on a run of the function whose symbol is
written `name`, with a choice budget of `budget` bits: every way its paths
end, each once, or that some path chooses more than the budget. -/
def exhaustiveReport (name : String) (budget : Nat) : Option (List (RunLeaf V × Nat)) → RunReport
  | none => { out := resultJson "choice-budget-exceeded" [("budget", toString budget)], status := 0 }
  | some ls => match ls.mapM (fun (l, c) => (pathFields (V := V) l.pathEnd).map (·, c)) with
    | .error op => noRules name op
    | .ok ps =>
      let choices := ps.foldl (fun m p => max m p.2) 0
      { out := resultJson "outcomes" [("choices", toString choices),
          ("outcomes", jsonArray (distinct (ps.map (jsonObject ·.1.1))))],
        status := if ps.any (·.1.2) then 1 else 0 }

/-! # The modes, by the machine

`runBytes` below calls the spec's `Gpu.scripted`, `Gpu.exhaustive` and
`Gpu.sampled`, the modes of the sum of the core and `gpu` at a work-item;
the core's own modes, `Core.scripted`, `Core.exhaustive` and
`Core.sampled`, are what it called before #212. The theorems here make Lean
compile calls of either as calls of
`FirRef.Machine`'s walks of the run
(`docs/decisions/fir-ref-fast-paths.md#running`), which take no stack per step,
per level of calls or per choice. They name the dialects in tree, so they
live in `fir-ref`'s command line, not in `FirRef.RunModes` (G0,
ADR-2026-11-03-0600).
-/

/-- `Core.scripted`, by the machine, with the core's semantics in the layer
over the tree that the modes run: each memory with its entry in `M`'s data
layout, named by its number. -/
def runScripted {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (M : Module CoreDialect)
    (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2))) (fuel : Nat)
    (cs : List σ) : Except (ChoiceTree.Misfit σ) (RunLeaf × Nat) :=
  letI := Core.memTreeDenote M.layout.entry id
  Machine.scripted (unit := unitsOf M.layout.entry) M read f args fuel cs

@[csimp] theorem scripted_eq_runScripted : @Core.scripted = @runScripted := by
  funext σ read M f args fuel cs
  letI := Core.memTreeDenote M.layout.entry id
  exact (Machine.scripted_eq M read f args fuel cs).symm

/-- `Core.exhaustive`, by the machine. -/
def runExhaustive (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) :
    Option (List (RunLeaf × Nat)) :=
  letI := Core.memTreeDenote M.layout.entry id
  Machine.exhaustive (unit := unitsOf M.layout.entry) M f args fuel budget

@[csimp] theorem exhaustive_eq_runExhaustive : @Core.exhaustive = @runExhaustive := by
  funext M f args fuel budget
  letI := Core.memTreeDenote M.layout.entry id
  exact (Machine.exhaustive_eq M f args fuel budget).symm

/-- `Core.sampled`, by the machine. -/
def runSampled {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (M : Module CoreDialect)
    (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    RunLeaf × List ChoiceTree.Chosen :=
  letI := Core.memTreeDenote M.layout.entry id
  Machine.sampled (unit := unitsOf M.layout.entry) M draw f args fuel g

@[csimp] theorem sampled_eq_runSampled : @Core.sampled = @runSampled := by
  funext γ draw M f args fuel g
  letI := Core.memTreeDenote M.layout.entry id
  exact (Machine.sampled_eq M draw f args fuel g).symm

/-- `Gpu.scripted`, by the machine, with
the semantics of the core and `gpu` at the work-item in the layer over the
tree: each memory with its entry in `M`'s data layout, named by its
number. -/
def runGpuScripted [Gpu.WorkItem] {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (M : Module CoreGpu) (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (cs : List σ) : Except (ChoiceTree.Misfit σ) (Gpu.Leaf × Nat) :=
  letI := Gpu.memTreeDenote M.layout.entry Gpu.memName
  Machine.scripted (unit := unitsOf M.layout.entry) M read f args fuel cs

@[csimp] theorem gpuScripted_eq_runGpuScripted : @Gpu.scripted = @runGpuScripted := by
  funext w σ read M f args fuel cs
  letI := Gpu.memTreeDenote M.layout.entry Gpu.memName
  exact (Machine.scripted_eq M read f args fuel cs).symm

/-- `Gpu.exhaustive`, by the machine. -/
def runGpuExhaustive [Gpu.WorkItem] (M : Module CoreGpu) (f : Func CoreGpu)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) :
    Option (List (Gpu.Leaf × Nat)) :=
  letI := Gpu.memTreeDenote M.layout.entry Gpu.memName
  Machine.exhaustive (unit := unitsOf M.layout.entry) M f args fuel budget

@[csimp] theorem gpuExhaustive_eq_runGpuExhaustive : @Gpu.exhaustive = @runGpuExhaustive := by
  funext w M f args fuel budget
  letI := Gpu.memTreeDenote M.layout.entry Gpu.memName
  exact (Machine.exhaustive_eq M f args fuel budget).symm

/-- `Gpu.sampled`, by the machine. -/
def runGpuSampled [Gpu.WorkItem] {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (M : Module CoreGpu) (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (g : γ) : Gpu.Leaf × List ChoiceTree.Chosen :=
  letI := Gpu.memTreeDenote M.layout.entry Gpu.memName
  Machine.sampled (unit := unitsOf M.layout.entry) M draw f args fuel g

@[csimp] theorem gpuSampled_eq_runGpuSampled : @Gpu.sampled = @runGpuSampled := by
  funext w γ draw M f args fuel g
  letI := Gpu.memTreeDenote M.layout.entry Gpu.memName
  exact (Machine.sampled_eq M draw f args fuel g).symm

/-- How `fir-ref run` walks a run: scripted mode, with a choice sequence,
exhaustive mode, with a choice budget in bits, or sampled mode, with the
seed of its generator. -/
inductive Mode where
  | scripted (choices : List String)
  | exhaustive (budget : Nat)
  | sampled (seed : Nat)
  deriving DecidableEq, Repr

/-- What `fir-ref run` reports on the bytes of `file`: it runs the function
that `func` names, a function of the module or a kernel of one of its
nested modules (`findFunc`), as the work-item `w`, on the arguments `args`,
with `fuel` steps, in the mode `mode`. -/
def runBytes (file : String) (bytes : ByteArray) (fuel : Nat) (func : String)
    (args : List String) (mode : Mode := .scripted []) (w : Gpu.WorkItem := .single) :
    RunReport :=
  letI := w
  match parseBytes (d := CoreGpu) bytes with
  | .error e => { err := s!"{file}:{e.pos.line}:{e.pos.col}: parse error: {e.reason}", status := 1 }
  | .ok m =>
    let what := if file == "-" then "standard input" else shown file
    match findFunc m func with
    | none => { err := s!"fir-ref: {what} has no function {shown func}", status := 2 }
    | some (n, f) =>
      let ts := f.params.map (·.2)
      let name := Text.printSymbol f.name
      if ts.length ≠ args.length then
        { err := s!"fir-ref: {shown func} takes {arguments ts.length}, not {args.length}",
          status := 2 }
      else match readGpuArgs ts args, mode with
        | .error why, _ => { err := s!"fir-ref: {why}", status := 2 }
        | .ok vs, .scripted cs =>
          scriptedReport name (Gpu.scripted constOf n f vs fuel cs)
        | .ok vs, .exhaustive b =>
          exhaustiveReport name b (Gpu.exhaustive n f vs fuel b)
        | .ok vs, .sampled s =>
          sampledReport name (Gpu.sampled draw n f vs fuel ⟨s.toUInt64⟩)

end FirRef
