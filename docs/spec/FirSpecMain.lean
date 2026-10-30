import VersoManual
import FirSpec

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

def main (args : List String) : IO UInt32 := do
  manualMain (%doc FirSpec) (options := args) (config := { extraContents := ← builtFrom })
