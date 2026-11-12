import Lean.Data.Json
import FirSpecSite.Citation

/-!
Every ADR citation in the spec's sources must name an ADR. The sources are
the Lean files of `lean/`, the files at the top of `docs/spec/` and the ADRs.
The check reads the files themselves, so each message gives the file, line
and column, and it also covers Lean comments, which the document shows as
code. A citation in a code span or a fenced code block is quoted, not cited,
and is not checked: the document shows it as code, without a link. A
citation of a deleted ADR, one with a row in `docs/adrs/removed/`, fails
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

/-- The directory of the tables of deleted ADRs, one per area, relative to the repository. -/
def removedDir : String := "docs/adrs/removed"

/--
Each deleted ADR's id and where its rule lives now, from the text of one
removed table. The `adr-ids` hook checks the rest of each row.
-/
def parseRemoved (text : String) : Except String (Array (String × String)) := do
  let table ← Lean.Json.parse text
  (← table.getObjValAs? (Array Lean.Json) "removed").mapM fun row => do
    let file ← row.getObjValAs? String "file"
    let some id := adrIdOfFileName? file | throw s!"{file} is not an ADR file name"
    return (id, ← row.getObjValAs? String "now")

/--
The rows of the tables of `removedDir` in the repository at `root`, in the
order of their names, or none when the directory is absent.
-/
def loadRemoved (root : System.FilePath) : IO (Except String (Array (String × String))) := do
  unless ← (root / removedDir).isDir do return .ok #[]
  let mut rows := #[]
  for file in (← filesUnder root removedDir (fun _ => true) (·.endsWith ".json")).qsort (· < ·) do
    match parseRemoved (← IO.FS.readFile (root / file)) with
    | .ok more => rows := rows ++ more
    | .error e => return .error s!"{file}: {e}"
  return .ok rows

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
that names a deleted ADR of `removedDir`.
-/
def checkSources (root : System.FilePath) (ids : Array String) : IO (Array String) := do
  let (removed, loadErrors) := match ← loadRemoved root with
    | .ok rows => (rows, #[])
    | .error e => (#[], #[e])
  let gone (id : String) := (removed.find? (·.1 == id)).map (·.2)
  let mut errors := loadErrors
  for file in ← sourceFiles root do
    errors := errors ++ checkText (ids.contains ·) gone file (← IO.FS.readFile (root / file))
  return errors

end FirSpecSite
