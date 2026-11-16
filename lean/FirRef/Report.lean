import Fir
import FirRef.Utf8
import FirRef.RunText

/-!
What `fir-ref validate` reports on a file: one JSON object on one line, in the
schema of `funk verify --json`
(`docs/decisions/rust-ir-and-tools-funk.md#report-format`), so that #13
compares the two tools' verdicts with no translation.
`docs/decisions/fir-ref-command-line.md#fir-ref-validate` records the schema.
The object has the file, its verdict and its diagnostics:

* `accepted`: the text parses and the module is valid, with no diagnostics;
* `parse-error`: one diagnostic with the parser's reason, and the line and
  column of the error (UTF-8 bytes from 1);
* `validation-error`: one diagnostic for each problem of the validation
  check, with the function, the block, the op's index and its location,
  each `null` when it does not apply;
* `io-error`: the file cannot be read.

Strings escape `"`, `\`, the line feed, the tab and the carriage return,
and every other character that a fir string escapes, as `\uXXXX` in UTF-16,
so a report holds no hidden character.
-/

namespace FirRef

open Fir

/-- Four lowercase hexadecimal digits. -/
def hex4 (n : Nat) : String :=
  let h := Text.hex n
  "".pushn '0' (4 - h.length) ++ h

/-- One character of a JSON string, escaped as `funk`'s reports escape it. -/
def jsonChar (c : Char) : String :=
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if c = '\n' then "\\n"
  else if c = '\t' then "\\t"
  else if c = '\r' then "\\r"
  else if Text.isEscaped c then
    let n := c.toNat
    if n < 0x10000 then "\\u" ++ hex4 n
    else
      let m := n - 0x10000
      "\\u" ++ hex4 (0xd800 + m / 0x400) ++ "\\u" ++ hex4 (0xdc00 + m % 0x400)
  else c.toString

/-- A JSON string. -/
def jsonString (s : String) : String := s.foldl (fun out c => out ++ jsonChar c) "\"" ++ "\""

/-- A JSON value that may be `null`. -/
def jsonOption {α : Type} (toJson : α → String) : Option α → String
  | none => "null"
  | some a => toJson a

/-- A JSON object, from its fields in order, each with its value's JSON. -/
def jsonObject (fields : List (String × String)) : String :=
  "{" ++ ",".intercalate (fields.map fun (k, v) => jsonString k ++ ":" ++ v) ++ "}"

/-- A JSON array, from its elements' JSON. -/
def jsonArray (items : List String) : String := "[" ++ ",".intercalate items ++ "]"

/-- A diagnostic of a kind with a message, and more fields. -/
def diagnostic (kind message : String) (more : List (String × String) := []) : String :=
  jsonObject ([("kind", jsonString kind), ("message", jsonString message)] ++ more)

/-- A problem of the validation check, as a diagnostic. `table` holds the
module's locations, by reference. -/
def problemJson (table : Std.HashMap LocRef Location) (p : Problem) : String :=
  let loc (r : LocRef) := jsonObject
    [("ref", toString r), ("location", jsonOption (jsonString ·.print) table[r]?)]
  diagnostic "validation-error" p.message
    [("func", jsonOption jsonString p.func), ("block", jsonOption jsonString p.block),
     ("op", jsonOption toString p.op), ("loc", jsonOption loc p.loc)]

/-- The report on a file, from its verdict and its diagnostics. -/
def report (file verdict : String) (diagnostics : List String) : String :=
  jsonObject [("file", jsonString file), ("verdict", jsonString verdict),
    ("diagnostics", jsonArray diagnostics)]

/-- The report on a file that cannot be read. -/
def ioErrorReport (file why : String) : String :=
  report file "io-error" [diagnostic "io-error" why]

/-- The report on a file whose text parses as the module `m`, and its exit
status: 0 when `m` is valid and keeps to its dialect set, 1 when it does
not. `fir-ref` checks `m` with `Module.problems` and `Module.setProblems`,
which run `FirRef.moduleProblems` and `FirRef.moduleSetProblems` here,
since this module is compiled after `FirRef.Fast`. It is written for any
dialect, so that the Lean tests check it on the core's modules; `fir-ref`
runs it on the sum of the core and `gpu`, `CoreGpu`. -/
def reportModule {d : Dialect} [DialectSignature d] [DialectValidation d]
    [DecidableDialectValidation d] [DecidableEq d.Ty] [DialectText d] [DialectSet d]
    (file : String) (m : Module d) : String × UInt32 :=
  match m.problems ++ m.setProblems with
  | [] => (report file "accepted" [], 0)
  | ps => (report file "validation-error" (ps.map (problemJson (firsts m.locs))), 1)

/-- The report on the bytes of a file, and its exit status: 0 when the file
is accepted, 1 when it is rejected. -/
def validateBytes (file : String) (bytes : ByteArray) : String × UInt32 :=
  match parseBytes (d := CoreGpu) bytes with
  | .error e =>
    (report file "parse-error" [diagnostic "parse-error" e.reason
      [("line", toString e.pos.line), ("column", toString e.pos.col)]], 1)
  | .ok m => reportModule file m

/-! # What `fir-ref run` reports

`fir-ref run` reports a result as one JSON object on one line, escaped as
`fir-ref validate`'s reports are
(`docs/decisions/fir-ref-command-line.md#results`). `FirRef.Run` computes the
result; the functions below write it.
-/

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

/-- The report of exhaustive mode that tries a few NaNs, `--exhaustive
--nans`, on a run of the function whose symbol is written `name`, with a
choice budget of `budget` bits: as exhaustive mode's, and whether the
outcomes are the whole set, `complete`, which they are when no path made a
NaN choice (`Gpu.exhaustiveNaN_exact`). -/
def exhaustiveNaNReport (name : String) (budget : Nat) :
    Option (List (RunLeaf V × Nat × Nat)) → RunReport
  | none => { out := resultJson "choice-budget-exceeded" [("budget", toString budget)], status := 0 }
  | some ls => match ls.mapM (fun (l, c, n) => (pathFields (V := V) l.pathEnd).map (·, c, n)) with
    | .error op => noRules name op
    | .ok ps =>
      let choices := ps.foldl (fun m p => max m p.2.1) 0
      { out := resultJson "outcomes" [("choices", toString choices),
          ("complete", if ps.all (·.2.2 == 0) then "true" else "false"),
          ("outcomes", jsonArray (distinct (ps.map (jsonObject ·.1.1))))],
        status := if ps.any (·.1.2) then 1 else 0 }

end FirRef
