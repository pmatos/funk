import Lean.Data.Json
import FirSpecSite.Citation

/-!
Every ADR citation in the spec's sources must name an ADR. The sources are
the Lean files of `lean/`, the files at the top of `docs/spec/` and the ADRs.
The check reads the files themselves, so each message gives the file, line
and column, and it also covers Lean comments, which the document shows as
code. A citation in a code span or a fenced code block is quoted, not cited,
and is not checked: the document shows it as code, without a link. A
citation of a deleted ADR, one with a row in `docs/adrs/removed.json`, fails
with where its rule lives now, as the `adr-citations` hook says it.
-/

namespace FirSpecSite

/--
The paths, relative to `root`, of the files under `dir` whose names satisfy
`keep`, skipping directories whose names satisfy `skip`. An empty `dir` is
`root` itself.
-/
partial def filesUnder (root : System.FilePath) (dir : String) (skip keep : String → Bool) :
    IO (Array String) := do
  let mut out := #[]
  for e in ← (root / dir).readDir do
    let path := if dir.isEmpty then e.fileName else s!"{dir}/{e.fileName}"
    if ← (root / path).isDir then
      unless skip e.fileName do
        out := out ++ (← filesUnder root path skip keep)
    else if keep e.fileName then
      out := out.push path
  return out

/-- The spec's sources, relative to the repository at `root`, in order. -/
def sourceFiles (root : System.FilePath) : IO (Array String) := do
  let lean ← filesUnder root "lean" (· == ".lake") (·.endsWith ".lean")
  let spec ← filesUnder root "docs/spec" (fun _ => true) fun n => n.endsWith ".lean" || n.endsWith ".md"
  let adrs ← filesUnder root "docs/adrs" (fun _ => true) (·.endsWith ".md")
  return (lean ++ spec ++ adrs).qsort (· < ·)

/-- The file of the rows of deleted ADRs, relative to the repository. -/
def removedFile : String := "docs/adrs/removed.json"

/--
Each deleted ADR's id and where its rule lives now, from the text of
`removed.json`. The `adr-ids` hook checks the rest of each row.
-/
def parseRemoved (text : String) : Except String (Array (String × String)) := do
  let table ← Lean.Json.parse text
  (← table.getObjValAs? (Array Lean.Json) "removed").mapM fun row => do
    let file ← row.getObjValAs? String "file"
    let some id := adrIdOfFileName? file | throw s!"{file} is not an ADR file name"
    return (id, ← row.getObjValAs? String "now")

/-- The rows of `removed.json` in the repository at `root`, or none when it is absent. -/
def loadRemoved (root : System.FilePath) : IO (Except String (Array (String × String))) := do
  unless ← (root / removedFile).pathExists do return .ok #[]
  return (parseRemoved (← IO.FS.readFile (root / removedFile))).mapError (s!"{removedFile}: {·}")

/--
One message per citation in `text`, the contents of `file`, that names no ADR.
`removed` gives where the rule of a deleted ADR lives now.
-/
def checkText (known : String → Bool) (removed : String → Option String) (file text : String) :
    Array String :=
  let cs := text.toList.toArray
  (citationsIn (blankCode cs)).filterMap fun c =>
    let (line, col) := lineColumn cs c.start
    if !c.wellFormed then
      some s!"{file}:{line}:{col}: {c.text} is not an ADR id, which ends in HHMM or HHMMSS"
    else if let some now := removed c.id then
      some s!"{file}:{line}:{col}: {c.text} was removed; its rule lives in {now} now (docs/adrs/INDEX.md, Removed)"
    else if !known c.id then
      some s!"{file}:{line}:{col}: {c.text} names no ADR in docs/adrs/"
    else none

/--
One message per citation in the spec's sources that names no ADR in `ids`, or
that names a deleted ADR of `removed.json`.
-/
def checkSources (root : System.FilePath) (ids : Array String) : IO (Array String) := do
  let removed ← match ← loadRemoved root with
    | .ok rows => pure rows
    | .error e => return #[e]
  let gone (id : String) := (removed.find? (·.1 == id)).map (·.2)
  let mut errors := #[]
  for file in ← sourceFiles root do
    errors := errors ++ checkText (ids.contains ·) gone file (← IO.FS.readFile (root / file))
  return errors

end FirSpecSite
