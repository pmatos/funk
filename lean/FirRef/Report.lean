import Fir
import FirRef.Utf8
import FirRef.RunText
import FirRef.Reach

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

/-- A pointer as `fir-ref run` spells it: `ptr(A, O)`, for the allocation
`A` it has provenance for and its offset `O`, or `ptr(none, O)`. -/
def ptrText (p : Memory.Pointer) : String :=
  let a := match p.prov with | some a => toString a | none => "none"
  s!"ptr({a}, {(Attr.int p.offset).print})"

/-- A value as `fir-ref run` spells it: as a constant of its type in text,
or `poison`. A float is written as the one float literal of its bits
(ADR-2026-11-11-1438). A pointer is written `ptr(A, O)`, for the
allocation `A` it has provenance for and its offset `O`, and
`ptr(none, O)` when it has no provenance. It names no address, which a
pointer has only once it is exposed (ADR-2026-11-09-1542). A run starts
with its table's globals, which take a memory's first ids, so the pointer
that the first `alloca` of a run gives in a memory with no global is
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
    | .value p => ptrText p

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

/-- The fields of the JSON object that report how a path ends, whose return
is seen as a value of type `R`, and whether it is stuck; or the op without
rules that the path reaches. -/
abbrev Fields (R : Type) := PathEnd R Core.Op → Except Core.Op (List (String × String) × Bool)

variable {R : Type} (fields : Fields R)

/-- The report of scripted mode on a run of the function whose symbol is
written `name`: the one path that the choices name, or why they do not fit
the run. -/
def scriptedReportWith (name : String) :
    Except (ChoiceTree.Misfit String) (ChoiceTree.Leaf Core.Op (Except Stuck (Result R)) × Nat) →
      RunReport
  | .error m => { err := s!"fir-ref: {name}: the choices do not fit the run: {misfitText m}",
                  status := 2 }
  | .ok (l, c) => match fields l.pathEnd with
    | .error op => noRules name op
    | .ok (fs, stuck) =>
      { out := jsonObject (fs ++ [("choices", toString c)]), status := if stuck then 1 else 0 }

/-- A value that a path chose, spelled as `--choices` takes it: as a
constant of its type. -/
def chosenText : ChoiceTree.Chosen → String
  | ⟨w, b⟩ => (Core.constAttr w b).print

/-- The report of sampled mode on a run of the function whose symbol is
written `name`: the one path that the generator draws, and the values it
drew on it. -/
def sampledReportWith (name : String) :
    ChoiceTree.Leaf Core.Op (Except Stuck (Result R)) × List ChoiceTree.Chosen → RunReport
  | (l, cs) => match fields l.pathEnd with
    | .error op => noRules name op
    | .ok (fs, stuck) =>
      { out := jsonObject (fs ++ [("choices", toString cs.length),
          ("sequence", jsonArray (cs.map (jsonString ∘ chosenText)))]),
        status := if stuck then 1 else 0 }

/-- The report of an exhaustive walk on a run of the function whose symbol
is written `name`, with a choice budget of `budget` bits: every way its
paths end, each once, with the fields `more` after the choices, or that some
path chooses more than the budget. -/
def outcomesReportWith (name : String) (budget : Nat) (more : List (String × String)) :
    Option (List (ChoiceTree.Leaf Core.Op (Except Stuck (Result R)) × Nat)) → RunReport
  | none => { out := resultJson "choice-budget-exceeded" [("budget", toString budget)], status := 0 }
  | some ls => match ls.mapM (fun (l, c) => (fields l.pathEnd).map (·, c)) with
    | .error op => noRules name op
    | .ok ps =>
      let choices := ps.foldl (fun m p => max m p.2) 0
      { out := resultJson "outcomes" ([("choices", toString choices)] ++ more ++
          [("outcomes", jsonArray (distinct (ps.map (jsonObject ·.1.1))))]),
        status := if ps.any (·.1.2) then 1 else 0 }

/-- The report of exhaustive mode on a run of the function whose symbol is
written `name`, with a choice budget of `budget` bits. -/
def exhaustiveReportWith (name : String) (budget : Nat) :
    Option (List (ChoiceTree.Leaf Core.Op (Except Stuck (Result R)) × Nat)) → RunReport :=
  outcomesReportWith fields name budget []

/-- The report of exhaustive mode that tries a few NaNs, `--exhaustive
--nans`, on a run of the function whose symbol is written `name`, with a
choice budget of `budget` bits: exhaustive mode's, with whether the
outcomes are the whole set, `complete`, which they are when no path made a
NaN choice (`Gpu.exhaustiveNaN_exact`). -/
def exhaustiveNaNReportWith (name : String) (budget : Nat)
    (r : Option (List (ChoiceTree.Leaf Core.Op (Except Stuck (Result R)) × Nat × Nat))) :
    RunReport :=
  let complete := if (r.getD []).all (·.2.2 == 0) then "true" else "false"
  outcomesReportWith fields name budget [("complete", complete)]
    (r.map (·.map fun (l, c, _) => (l, c)))

/-! # The reports that see a return as its values -/

/-- The report of scripted mode, each return seen as its values. -/
def scriptedReport (name : String) :
    Except (ChoiceTree.Misfit String) (RunLeaf V × Nat) → RunReport :=
  scriptedReportWith (pathFields (V := V)) name

/-- The report of sampled mode, each return seen as its values. -/
def sampledReport (name : String) : RunLeaf V × List ChoiceTree.Chosen → RunReport :=
  sampledReportWith (pathFields (V := V)) name

/-- The report of exhaustive mode, each return seen as its values. -/
def exhaustiveReport (name : String) (budget : Nat) : Option (List (RunLeaf V × Nat)) → RunReport :=
  exhaustiveReportWith (pathFields (V := V)) name budget

/-- The report of exhaustive mode that tries a few NaNs, each return seen as
its values. -/
def exhaustiveNaNReport (name : String) (budget : Nat) (r : Option (List (RunLeaf V × Nat × Nat))) :
    RunReport :=
  exhaustiveNaNReportWith (pathFields (V := V)) name budget r

/-! # What `fir-ref run --world` reports

With a scripted world, each object that reports how a path ends also has
the path's trace and, at a return, what escaped and the memory that an
observer reaches, so that a judge can compare two runs as the spec's end of
a return does (`ObservedEnd`), up to a one-to-one renaming of allocations,
with no address compared (`docs/decisions/fir-ref-run-end.md#results`).
Neither the core nor `gpu` shows an event yet, so the trace is empty. A
unit is spelled `0x` and its bits in hexadecimal, `poison`, or the fragment
`I` of a pointer of the memory `N`, `frag(N, ptr(A, O), I)`; no address is
printed.
-/

open Memory

/-- The bits of a unit `u` bits wide, as `0x` and `⌈u/4⌉` lowercase
hexadecimal digits, at least one. -/
def unitBitsText (u : Nat) (b : BitVec u) : String :=
  let h := Text.hex b.toNat
  "0x" ++ "".pushn '0' (max 1 ((u + 3) / 4) - h.length) ++ h

/-- A unit of memory as `fir-ref run --world` spells it. -/
def unitText {u : Nat} : MemUnit u → String
  | .bits b => unitBitsText u b
  | .poison => "poison"
  | .frag m p i => s!"frag({m}, {ptrText p}, {i})"

/-- An allocation, by its memory and its id. -/
def allocRef (xa : Nat × AllocId) : List (String × String) :=
  [("memory", toString xa.1), ("alloc", toString xa.2)]

variable {unit : Nat → Nat}

/-- An allocation of the memories `S` that an observer reaches: its memory
and id, and its block's kind, alignment, size and liveness, with its units
while it is live; or a `null` kind when the memory never made it. -/
def allocJson (S : Memories Nat unit) (xa : Nat × AllocId) : String :=
  match (S.mem xa.1).blocks[xa.2]? with
  | none => jsonObject (allocRef xa ++ [("kind", "null")])
  | some b =>
    jsonObject (allocRef xa ++ [("kind", jsonString b.kind.word),
      ("align", toString b.align), ("size", toString b.units.length),
      ("live", if b.live then "true" else "false")] ++
      if b.live then [("units", jsonArray (b.units.map (jsonString ∘ unitText)))] else [])

/-- The fields that report the end of a return, after its values: its trace,
which is empty, the allocations that escaped, and the memory that an
observer reaches, or `null` when the walk runs out of steps, which its
bound is argued, not proved, to rule out (`FirRef.Reach`). -/
def endJson {ar : AddrRule} {V : Type} [HRefinement V V] [HasPtrs V] (e : End unit id ar V) :
    List (String × String) :=
  [("trace", "[]"), ("escaped", jsonArray (e.escaped.map (jsonObject ∘ allocRef))),
    ("memory", match endReach e with
      | some L => jsonArray (L.map (allocJson e.mem))
      | none => "null")]

/-- The fields that report how a path ends, each return seen at its end
(`Gpu.RunEnd`): those of `pathFields`, with the trace of every path after
its values or its reason, and at a return the allocations that escaped and
the memory that an observer reaches. -/
def endFields [Gpu.WorkItem] {M : Module CoreGpu} : Fields (Gpu.RunEnd M) := fun p =>
  (pathFields (V := DVal CoreGpu) (vals p)).map fun (fs, st) => (fs ++ more p, st)
where
  vals : PathEnd (Gpu.RunEnd M) Core.Op → PathEnd (List (DVal CoreGpu)) Core.Op
    | .outcome (.ret e) => .outcome (.ret e.vals)
    | .outcome (.ub r) => .outcome (.ub r)
    | .outcome .fuelExhausted => .outcome .fuelExhausted
    | .stuck st => .stuck st
    | .noOutcome op => .noOutcome op
  more : PathEnd (Gpu.RunEnd M) Core.Op → List (String × String)
    | .outcome (.ret e) => endJson e
    | _ => [("trace", "[]")]

/-- Why a scripted world does not fit a run that shows no event: it
answers some. -/
def worldMisfit (name : String) (answers : Nat) : RunReport :=
  { err := s!"fir-ref: {name}: the world's script does not fit the run: the run shows no " ++
      s!"event, and the script answers {answers}", status := 2 }

end FirRef
