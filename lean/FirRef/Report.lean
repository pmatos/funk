import Fir
import FirRef.Utf8

/-!
What `fir-ref validate` reports on a file: one JSON object on one line, in
the schema of `funk verify --json` (ADR-2026-10-30-1032), so that #13
compares the two tools' verdicts with no translation. ADR-2026-10-30-1741
records the schema. The object has the file, its verdict and its
diagnostics:

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

/-- The report on the bytes of a file, and its exit status: 0 when the file
is accepted, 1 when it is rejected. -/
def validateBytes (file : String) (bytes : ByteArray) : String × UInt32 :=
  match parseBytes (d := CoreDialect) bytes with
  | .error e =>
    (report file "parse-error" [diagnostic "parse-error" e.reason
      [("line", toString e.pos.line), ("column", toString e.pos.col)]], 1)
  | .ok m =>
    match m.problems with
    | [] => (report file "accepted" [], 0)
    | ps => (report file "validation-error" (ps.map (problemJson (firsts m.locs))), 1)

end FirRef
