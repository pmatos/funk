import Std.Data.HashSet
import Fir
import FirRef.Utf8
import FirRef.Report

/-!
What `fir-ref run` does with a file: it parses it with the core dialect,
runs one of its functions with the spec's interpreter, `Func.run`, and
reports the result as one JSON object on one line (ADR-2026-10-30-1856,
ADR-2026-10-30-2218).

`freeze` of poison makes a choice, so a run may end in many ways.
`fir-ref` runs the interpreter in the spec's tree of choices, with the
core dialect's rules, and walks the tree in one of two modes, the spec's
`Core.scripted` and `Core.exhaustive`, which Lean proves sound
(`Core.scripted_outcomes`, `Core.exhaustive_outcomes`):

* scripted mode, the default, follows the one path that a choice sequence
  names, given with `--choices`, and reports its one outcome. With no
  `--choices`, the sequence is empty, so a run that makes no choice is
  reported as before #14, with a count of `0` choices, and one that makes
  a choice is an error;
* exhaustive mode, `--exhaustive`, reports every outcome of the run, when
  no path chooses more bits in all than its budget, `--choice-bits`.

Both say how many choices a path made. An op without rules has no outcome
in the spec, so a path that reaches one is reported as an error, not as a
result (ADR-2026-10-30-1855), and so is a choice sequence that does not
fit the run.

Arguments, choices and values are spelled as constants are in text: `true`
and `false` at `i1`, and signed decimal at every other width, read with the
spec's lexer and checked with `Core.Op.decode`. A value may also be
`poison`; an argument or a choice may not.
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
or `poison`. -/
def valueText : DVal CoreDialect → String
  | ⟨.int w, v⟩ => match (v : PoisonOr (BitVec w)) with
    | .poison => "poison"
    | .value b => (Core.constAttr w b).print
  | ⟨.ptr, v⟩ => nomatch (v : Empty)

/-- The constant that the text `s` spells at the type `iN`: the spec's
lexer reads `s` as one token, `Core.Op.decode` reads that as a `const`, and
the token is spelled exactly `s`, with nothing around it. -/
def constOf (w : Nat) (s : String) : Option (BitVec w) := do
  let attr ← match Text.lex s with
    | .ok [⟨.int i, _⟩, ⟨.eof, _⟩] => some (Attr.int i)
    | .ok [⟨.word x, _⟩, ⟨.eof, _⟩] => some (Attr.word x)
    | _ => none
  if attr.print != s then none
  match Core.Op.decode "const" [attr] [] [.int w] with
  | some (.const w' v) => if h : w' = w then some (h ▸ v) else none
  | _ => none

/-- An argument of type `t`: a constant of `t`. -/
def readArg : (t : Core.Ty) → String → Except String ⟦t⟧
  | .int w, s => match constOf w s with
    | some v => pure (.value v : PoisonOr (BitVec w))
    | none => .error s!"{shown s} is not a value of type {tyText (.int w)}"
  | .ptr, s => .error s!"{shown s} is not a value of type ptr"

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
(ADR-2026-10-30-1855). -/
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

/-- How `fir-ref run` walks a run: scripted mode, with a choice sequence,
or exhaustive mode, with a choice budget in bits. -/
inductive Mode where
  | scripted (choices : List String)
  | exhaustive (budget : Nat)
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
        | .ok vs, .scripted cs => scriptedReport name (Core.scripted constOf f vs fuel cs)
        | .ok vs, .exhaustive b => exhaustiveReport name b (Core.exhaustive f vs fuel b)

end FirRef
