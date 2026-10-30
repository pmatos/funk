import VersoManual
import FirSpec
import FirSpecSite

open Verso.Genre Manual
open Verso.Output Html

/--
The line on every page that names the commit the document was built from.
`scripts/build-spec.sh` sets `FIRSPEC_COMMIT`, and `FIRSPEC_COMMIT_URL` when
the commit has a web page. They are read when the document is rendered, not
when it is elaborated, so a warm build never shows a stale commit.
-/
def builtFrom : IO (Array Html) := do
  let some commit ← IO.getEnv "FIRSPEC_COMMIT" | return #[]
  let name : Html := {{<code>{{commit}}</code>}}
  let name := match ← IO.getEnv "FIRSPEC_COMMIT_URL" with
    | some url => {{<a href={{url}}>{{name}}</a>}}
    | none => name
  return #[{{<p class="fir-built-from"><small>"Built from commit " {{name}} "."</small></p>}}]

/-- Where `manualMain` writes the multi-page site, given the same options. -/
def htmlMultiDir (args : List String) : Option System.FilePath :=
  if args.contains "--without-html-multi" then none else
  let rec dest : List String → System.FilePath
    | "--output" :: dir :: _ => dir
    | _ :: more => dest more
    | [] => "_out"
  some (dest args / "html-multi")

/--
Renders the document with its appendix of ADRs and its ADR citations linked
(ADR-2026-10-30-1439), then checks the citations on the rendered pages. It
runs in `docs/spec/`, two levels below the repository's root.
-/
def main (args : List String) : IO UInt32 := do
  let report (errors : Array String) : IO UInt32 := do
    errors.forM (IO.eprintln ·)
    return 1
  match ← FirSpecSite.prepare "../.." (%doc FirSpec) with
  | .error errors => report errors
  | .ok (doc, ids) =>
    let status ← manualMain doc (options := args) (config := { extraContents := ← builtFrom })
    if status != 0 then return status
    let some dir := htmlMultiDir args | return 0
    let errors ← FirSpecSite.checkRendered dir ids
    if errors.isEmpty then return 0 else report errors
