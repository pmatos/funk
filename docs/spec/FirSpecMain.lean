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

/--
Where `manualMain` writes the multi-page site, given the same options: the
last `--output`, and none when the last of `--with-html-multi` and
`--without-html-multi` turns it off.
-/
def htmlMultiDir (args : List String) (dir : System.FilePath := "_out") (on : Bool := true) :
    Option System.FilePath :=
  match args with
  | "--output" :: dir :: more => htmlMultiDir more dir on
  | "--with-html-multi" :: more => htmlMultiDir more dir true
  | "--without-html-multi" :: more => htmlMultiDir more dir false
  | _ :: more => htmlMultiDir more dir on
  | [] => if on then some (dir / "html-multi") else none

#guard htmlMultiDir [] == some ("_out" / "html-multi" : System.FilePath)
#guard htmlMultiDir ["--output", "a", "--verbose", "--output", "b"] == some ("b" / "html-multi" : System.FilePath)
#guard htmlMultiDir ["--without-html-multi"] == none
#guard htmlMultiDir ["--without-html-multi", "--with-html-multi"] == some ("_out" / "html-multi" : System.FilePath)

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
    let config : RenderConfig := {
      extraContents := ← builtFrom
      extraCss := {CSS.mk FirSpecSite.adrIndexCss}
    }
    let status ← manualMain doc (options := args) (config := config)
    if status != 0 then return status
    let some dir := htmlMultiDir args | return 0
    let errors ← FirSpecSite.checkRendered dir ids
    if errors.isEmpty then return 0 else report errors
