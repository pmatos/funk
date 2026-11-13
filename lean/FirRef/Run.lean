import Std.Data.HashSet
import Fir
import FirRef.Utf8
import FirRef.Report
import FirRef.Sample
import FirRef.RunModes

/-!
What `fir-ref run` does with a file: it parses it with the core dialect, runs
one of its functions with the spec's interpreter, `Func.run`, and reports the
result as one JSON object on one line
(`docs/decisions/fir-ref-command-line.md#fir-ref-run`).

`freeze` of poison makes a choice, so a run may end in many ways.
`fir-ref` runs the interpreter in the state layer over the spec's tree of
choices, from the empty memories, with the core dialect's rules, and walks
the tree in one of three modes, the
spec's `Core.scripted`, `Core.exhaustive` and `Core.sampled`, which Lean
proves sound (`Core.scripted_outcomes`, `Core.exhaustive_outcomes`,
`Core.sampled_outcomes`, and for the runs with memory
`Core.scripted_memOutcomes`, `Core.exhaustive_memOutcomes` and
`Core.sampled_memOutcomes`):

* scripted mode, the default, follows the one path that a choice sequence
  names, given with `--choices`, and reports its one outcome. With no
  `--choices`, the sequence is empty, so a run that makes no choice
  reports its one outcome, with a count of `0` choices, and one that makes
  a choice is an error;
* exhaustive mode, `--exhaustive`, reports every outcome of the run, when
  no path chooses more bits in all than its budget, `--choice-bits`;
* sampled mode, `--seed`, follows the path on which a generator seeded
  with its number draws each choice, the spec's `Core.sampled`, and
  reports its one outcome and the values it drew, a sequence that
  `--choices` takes (`Core.sampled_fits`).

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

/-- The default budget of `fir-ref run`: a million steps. -/
def defaultFuel : Nat := 1000000

/-- The default choice budget of exhaustive mode: 16 bits in all on one
path, so at most 65,536 paths. -/
def defaultChoiceBits : Nat := 16

/-- Text from the command line, with each control character shown as
`\xHH`, so that a message stays on one line. -/
def shown (s : String) : String :=
  s.foldl (fun out c =>
    if c.toNat < 0x20 || c.toNat == 0x7f then
      out ++ "\\x" ++ (if c.toNat < 0x10 then "0" else "") ++ Text.hex c.toNat
    else out.push c) ""

/-- A type as text writes it, such as `i8`. -/
def tyText (t : Core.Ty) : String := t.attr.print

/-- An op as text writes its name and attributes, such as `add nsw`. -/
def opText (op : Core.Op) : String := " ".intercalate (op.name :: op.attrs.map Attr.print)

/-- A value as `fir-ref run` spells it: as a constant of its type in text,
or `poison`. A float is written as the one float literal of its bits
(ADR-2026-11-11-1438). A pointer is written `ptr(A, O)`, for the
allocation `A` it has provenance for and its offset `O`, and
`ptr(none, O)` when it has no provenance. It names no address, which a
pointer has only once it is exposed (ADR-2026-11-09-1542), and no run
gives one until an op makes a pointer (#231). -/
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

/-- `n` of a thing, in words: `1 argument`, `2 arguments`. -/
def count (n : Nat) (thing : String) : String := if n = 1 then s!"1 {thing}" else s!"{n} {thing}s"

/-- `n` arguments, in words. -/
def arguments (n : Nat) : String := count n "argument"

/-- The JSON object that reports a result of `kind`, with more fields. Its
strings are escaped as `fir-ref validate`'s are. -/
def resultJson (kind : String) (more : List (String × String) := []) : String :=
  jsonObject (("kind", jsonString kind) :: more)

/-- What `fir-ref run` writes: its standard output and its standard error,
each one line or empty, and its exit status. -/
structure RunReport where
  out : String := ""
  err : String := ""
  status : UInt32
  deriving DecidableEq, Repr

/-- A leaf of a run's tree, as `fir-ref run` sees it. -/
abbrev RunLeaf := ChoiceTree.Leaf Core.Op (Except Stuck (Result Core.Obs))

/-- The fields of the JSON object that reports how a path ends, other than
the choices it made, and whether it is stuck; or the op without rules that
the path reaches. -/
def pathFields : PathEnd Core.Obs Core.Op → Except Core.Op (List (String × String) × Bool)
  | .outcome (.ret vs) =>
    .ok ([("kind", jsonString "return"), ("values", jsonArray (vs.map (jsonString ∘ valueText)))],
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
def scriptedReport (name : String) : Except (ChoiceTree.Misfit String) (RunLeaf × Nat) → RunReport
  | .error m => { err := s!"fir-ref: {name}: the choices do not fit the run: {misfitText m}",
                  status := 2 }
  | .ok (l, c) => match pathFields l.pathEnd with
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
def sampledReport (name : String) : RunLeaf × List ChoiceTree.Chosen → RunReport
  | (l, cs) => match pathFields l.pathEnd with
    | .error op => noRules name op
    | .ok (fields, stuck) =>
      { out := jsonObject (fields ++ [("choices", toString cs.length),
          ("sequence", jsonArray (cs.map (jsonString ∘ chosenText)))]),
        status := if stuck then 1 else 0 }

/-- Each element once, in the order it first appears. -/
def distinct (xs : List String) : List String :=
  (xs.foldl (fun (seen, out) x => if seen.contains x then (seen, out) else (seen.insert x, out.push x))
    ((∅ : Std.HashSet String), (#[] : Array String))).2.toList

/-- The report of exhaustive mode on a run of the function whose symbol is
written `name`, with a choice budget of `budget` bits: every way its paths
end, each once, or that some path chooses more than the budget. -/
def exhaustiveReport (name : String) (budget : Nat) : Option (List (RunLeaf × Nat)) → RunReport
  | none => { out := resultJson "choice-budget-exceeded" [("budget", toString budget)], status := 0 }
  | some ls => match ls.mapM (fun (l, c) => (pathFields l.pathEnd).map (·, c)) with
    | .error op => noRules name op
    | .ok ps =>
      let choices := ps.foldl (fun m p => max m p.2) 0
      { out := resultJson "outcomes" [("choices", toString choices),
          ("outcomes", jsonArray (distinct (ps.map (jsonObject ·.1.1))))],
        status := if ps.any (·.1.2) then 1 else 0 }

/-! # The modes, by the machine

`runBytes` below calls the spec's `Core.scripted`, `Core.exhaustive` and
`Core.sampled`. The theorems here make Lean compile those calls as calls of
`FirRef.Machine`'s walks of the run
(`docs/decisions/fir-ref-fast-paths.md#running`), which take no stack per step,
per level of calls or per choice. They name the core dialect, so they live in
`fir-ref`'s command line, not in `FirRef.RunModes` (G0, ADR-2026-11-03-0600).
-/

/-- `Core.scripted`, by the machine. -/
def runScripted {N : Type} [DecidableEq N] (unit : N → Nat) {σ : Type}
    (read : (w : Nat) → σ → Option (BitVec w)) (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ) :
    Except (ChoiceTree.Misfit σ) (RunLeaf × Nat) :=
  Machine.scripted (unit := unit) M read f args fuel cs

@[csimp] theorem scripted_eq_runScripted : @Core.scripted = @runScripted := by
  funext N _ unit σ read M f args fuel cs
  exact (Machine.scripted_eq M read f args fuel cs).symm

/-- `Core.exhaustive`, by the machine. -/
def runExhaustive {N : Type} [DecidableEq N] (unit : N → Nat) (M : Module CoreDialect)
    (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) :
    Option (List (RunLeaf × Nat)) :=
  Machine.exhaustive (unit := unit) M f args fuel budget

@[csimp] theorem exhaustive_eq_runExhaustive : @Core.exhaustive = @runExhaustive := by
  funext N _ unit M f args fuel budget
  exact (Machine.exhaustive_eq M f args fuel budget).symm

/-- `Core.sampled`, by the machine. -/
def runSampled {N : Type} [DecidableEq N] (unit : N → Nat) {γ : Type}
    (draw : (w : Nat) → γ → BitVec w × γ) (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    RunLeaf × List ChoiceTree.Chosen :=
  Machine.sampled (unit := unit) M draw f args fuel g

@[csimp] theorem sampled_eq_runSampled : @Core.sampled = @runSampled := by
  funext N _ unit γ draw M f args fuel g
  exact (Machine.sampled_eq M draw f args fuel g).symm

/-- The width of the units of each memory of a run of `fir-ref` on a module
whose data layout is `l`, which names the core's memories by themselves
(`docs/decisions/fir-ref-memory.md#the-modes-run-with-memory`): the unit of
the memory's entry in `l`. Memory 0 has an entry in every layout. A memory
that `l` does not declare gets the default memory's unit; no op of a valid
module reaches it, since validation rejects every pointer type that names
it. -/
def coreUnit (l : DataLayout) : Core.Mem → Nat := fun n => ((l.memory? n).getD .default).unit

/-- How `fir-ref run` walks a run: scripted mode, with a choice sequence,
exhaustive mode, with a choice budget in bits, or sampled mode, with the
seed of its generator. -/
inductive Mode where
  | scripted (choices : List String)
  | exhaustive (budget : Nat)
  | sampled (seed : Nat)
  deriving DecidableEq, Repr

/-- What `fir-ref run` reports on the bytes of `file`: it runs the function
that `func` names, as text writes its symbol, on the arguments `args`, with
`fuel` steps, in the mode `mode`. -/
def runBytes (file : String) (bytes : ByteArray) (fuel : Nat) (func : String)
    (args : List String) (mode : Mode := .scripted []) : RunReport :=
  match parseBytes (d := CoreDialect) bytes with
  | .error e => { err := s!"{file}:{e.pos.line}:{e.pos.col}: parse error: {e.reason}", status := 1 }
  | .ok m =>
    let what := if file == "-" then "standard input" else shown file
    match m.funcs.find? (Text.printSymbol ·.name == func) with
    | none => { err := s!"fir-ref: {what} has no function {shown func}", status := 2 }
    | some f =>
      let ts := f.params.map (·.2)
      let name := Text.printSymbol f.name
      if ts.length ≠ args.length then
        { err := s!"fir-ref: {shown func} takes {arguments ts.length}, not {args.length}",
          status := 2 }
      else match readArgs ts args, mode with
        | .error why, _ => { err := s!"fir-ref: {why}", status := 2 }
        | .ok vs, .scripted cs =>
          scriptedReport name (Core.scripted (coreUnit m.layout) constOf m f vs fuel cs)
        | .ok vs, .exhaustive b =>
          exhaustiveReport name b (Core.exhaustive (coreUnit m.layout) m f vs fuel b)
        | .ok vs, .sampled s =>
          sampledReport name (Core.sampled (coreUnit m.layout) draw m f vs fuel ⟨s.toUInt64⟩)

end FirRef
