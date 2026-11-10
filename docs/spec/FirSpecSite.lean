import FirSpecSite.Citation
import FirSpecSite.Markdown
import FirSpecSite.Adr
import FirSpecSite.Link
import FirSpecSite.Sources
import FirSpecSite.Modules
import FirSpecSite.Rendered

/-!
What `firspec` adds to the document before Verso renders it, and what it
checks after: the appendix of ADRs and the links of ADR citations
(ADR-2026-10-30-1439).
-/

namespace FirSpecSite

/--
The style of a section title's permalink icon on a narrow screen, up to the
700px at which Verso's own style changes. Verso, at `v4.35.0`, positions the
icon's link absolutely and shows it only on hover. So the icon takes no room in
the line, sticks out past the end of a title that fills its line, and the page
scrolls sideways. Here the icon is in the flow of the line and always shown, as
Verso shows its block permalinks on a narrow screen. A word joiner keeps it on
the line of the title's last word; it moves alone only after a space. Re-check
this rule when Verso is bumped.
-/
def headingCss : String :=
  let icon := ":is(h1, h2, h3, h4, h5, h6) > .permalink-widget.inline"
  "@media screen and (max-width: 700px) {\n" ++
  s!"  {icon} \{ opacity: 1; }\n" ++
  s!"  {icon}::before \{ content: \"\\2060\"; }\n" ++
  s!"  {icon} > a \{ position: static; }\n" ++
  "}\n"

/--
The document `doc` with its appendix of ADRs filled and every ADR citation
linked, read from the repository at `root`, together with the ADRs' ids. Fails
with one message per problem: an ADR that cannot be rendered, or a citation
in the spec's sources or the document that names no ADR or cannot be a link.
-/
def prepare (root : System.FilePath) (doc : Prt) : IO (Except (Array String) (Prt × Array String)) := do
  unless ← (root / adrDir).isDir do
    return .error #[s!"{root / adrDir} is not a directory; run firspec from docs/spec"]
  match ← loadAdrs root with
  | .error errors => return .error errors
  | .ok adrs =>
    let ids := adrs.map (·.id)
    let errors := (← checkSources root ids) ++ (← checkModules root)
    unless errors.isEmpty do return .error errors
    match addAppendix doc adrs with
    | .error e => return .error #[e]
    | .ok doc => return (linkCitations adrs doc).map (·, ids)

end FirSpecSite
