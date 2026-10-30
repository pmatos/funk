import FirSpecSite.Citation
import FirSpecSite.Markdown
import FirSpecSite.Adr
import FirSpecSite.Link
import FirSpecSite.Sources
import FirSpecSite.Rendered

/-!
What `firspec` adds to the document before Verso renders it, and what it
checks after: the appendix of ADRs and the links of ADR citations
(ADR-2026-10-30-1439).
-/

namespace FirSpecSite

/--
The document `doc` with its appendix of ADRs filled and every ADR citation
linked, read from the repository at `root`, together with the ADRs' ids. Fails
with one message per problem: an ADR that cannot be rendered, or a citation
in the spec's sources or the document that names no ADR.
-/
def prepare (root : System.FilePath) (doc : Prt) : IO (Except (Array String) (Prt × Array String)) := do
  unless ← (root / adrDir).isDir do
    return .error #[s!"{root / adrDir} is not a directory; run firspec from docs/spec"]
  match ← loadAdrs root with
  | .error errors => return .error errors
  | .ok adrs =>
    let ids := adrs.map (·.id)
    let errors ← checkSources root ids
    unless errors.isEmpty do return .error errors
    match addAppendix doc adrs with
    | .error e => return .error #[e]
    | .ok doc => return (linkCitations ids doc).map (·, ids)

end FirSpecSite
