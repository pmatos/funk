import Fir
import FirRef.Utf8
import FirRef.Report

/-!
What `fir-ref run` does with a file: it parses it with the core dialect,
runs one of its functions with the spec's interpreter, `Func.run`, and
reports the result as one JSON object on one line (ADR-2026-10-30-1856).

A run has one path until #14 gives `freeze` its choice, so `fir-ref` runs
the interpreter in `Exec`, a monad with one path that may end early: with
immediate UB, or at an op that has no execution rules yet. The rules are
the spec's, `Core.Op.denote?` and `Core.Op.exit?`, the same rules that
`DialectDenote CoreDialect SetM` gives. An op without rules has no outcome
in the spec, so `fir-ref` reports it as an error, not as a result
(ADR-2026-10-30-1855).

Arguments and values are spelled as constants are in text: `true` and
`false` at `i1`, and signed decimal at every other width, read with the
spec's lexer and checked with `Core.Op.decode`. A value may also be
`poison`; an argument may not.
-/

namespace FirRef

open Fir

/-- What ends a run of `fir-ref` early: immediate UB, or an op that has no
execution rules yet. -/
inductive Halt where
  | ub (reason : String)
  | noRules (op : Core.Op)

/-- The monad that `fir-ref run` computes in: one path, which may end
early. -/
abbrev Exec := Except Halt

instance : MonadUB Exec := ⟨fun r => throw (.ub r)⟩

/-- The core dialect's rules, in `Exec`. -/
instance : DialectDenote CoreDialect Exec where
  denote op args := match op.denote? (m := Exec) with
    | some rule => rule args
    | none => throw (.noRules op)
  exit op args := match op.exit? (m := Exec) with
    | some rule => rule args
    | none => throw (.noRules op)

/-- The default budget of `fir-ref run`: a million steps. -/
def defaultFuel : Nat := 1000000

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

/-- `n` arguments, in words. -/
def arguments (n : Nat) : String := if n = 1 then "1 argument" else s!"{n} arguments"

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

/-- The report on a run, in `Exec`, of the function whose symbol is
written `name`: its JSON, and the exit status of ADR-2026-10-30-1856. -/
def outcomeReport (name : String) : Exec (Except Stuck (Result Core.Obs)) → RunReport
  | .ok (.ok (.ret vs)) =>
    { out := resultJson "return" [("values", jsonArray (vs.map (jsonString ∘ valueText)))],
      status := 0 }
  | .ok (.ok .fuelExhausted) => { out := resultJson "fuel-exhausted", status := 0 }
  | .ok (.error st) => { out := resultJson "stuck" [("reason", jsonString st.reason)], status := 1 }
  | .error (.ub r) => { out := resultJson "ub" [("reason", jsonString r)], status := 0 }
  | .error (.noRules op) =>
    { err := s!"fir-ref: {name}: {opText op} has no execution rules yet", status := 2 }

/-- What `fir-ref run` reports on the bytes of `file`: it runs the function
that `func` names, as text writes its symbol, on the arguments `args`, with
`fuel` steps. -/
def runBytes (file : String) (bytes : ByteArray) (fuel : Nat) (func : String)
    (args : List String) : RunReport :=
  match parseBytes (d := CoreDialect) bytes with
  | .error e => { err := s!"{file}:{e.pos.line}:{e.pos.col}: parse error: {e.reason}", status := 1 }
  | .ok m =>
    let what := if file == "-" then "standard input" else shown file
    match m.funcs.find? (Text.printSymbol ·.name == func) with
    | none => { err := s!"fir-ref: {what} has no function {shown func}", status := 2 }
    | some f =>
      let ts := f.params.map (·.2)
      if ts.length ≠ args.length then
        { err := s!"fir-ref: {shown func} takes {arguments ts.length}, not {args.length}",
          status := 2 }
      else match readArgs ts args with
        | .error why => { err := s!"fir-ref: {why}", status := 2 }
        | .ok vs => outcomeReport (Text.printSymbol f.name) (f.run (m := Exec) vs fuel).run

/-- The arguments of `run`: its fuel, its file, the function and the
function's arguments. -/
structure RunArgs where
  fuel : Nat
  file : String
  func : String
  args : List String

/-- Reads the arguments of `run`. `--fuel N` may come anywhere before `--`,
which ends the options, and N is ASCII decimal digits; an argument such as
`-5` is not an option. -/
def runArgs (args : List String) : Except String RunArgs := go true defaultFuel [] args
where
  go (options : Bool) (fuel : Nat) (pos : List String) : List String → Except String RunArgs
    | [] => match pos.reverse with
      | file :: func :: rest => .ok ⟨fuel, file, func, rest⟩
      | [_] => .error "no @FUNC given"
      | [] => .error "no FILE given; use - for standard input"
    | a :: rest =>
      if options && a == "--" then go false fuel pos rest
      else if options && a == "--fuel" then
        match rest with
        | n :: rest' =>
          match if n.all Char.isDigit then n.toNat? else none with
          | some k => go options k pos rest'
          | none => .error s!"--fuel takes a number of steps, not {shown n}"
        | [] => .error "--fuel takes a number of steps"
      else if options && a.startsWith "--" then .error s!"unknown option {shown a}"
      else go options fuel (a :: pos) rest

end FirRef
