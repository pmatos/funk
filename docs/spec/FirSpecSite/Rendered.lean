import Lean.Data.Json
import FirSpecSite.Citation

/-!
A check of the rendered pages. Every ADR has a page, and every ADR citation
in the prose of every page sits inside a link to that ADR's page. Prose is
the text in `<main>`, outside code, headings, navigation, scripts and styles.
It reads the HTML that Verso wrote, so it also catches a citation that the
linking pass never saw.
-/

namespace FirSpecSite

/-- The address of the page of ADR `id`, relative to the site's root. -/
def adrHref (id : String) : String := s!"adrs/ADR-{id}/#ADR-{id}"

private def skipped : List String :=
  ["code", "pre", "nav", "h1", "h2", "h3", "h4", "h5", "h6", "title"]

private def startsAt (cs : Array Char) (i : Nat) (s : String) : Bool :=
  s.toList.zipIdx.all fun (c, k) => cs[i + k]? == some c

private def findFrom (cs : Array Char) (i : Nat) (s : String) : Nat := Id.run do
  let mut j := i
  while j < cs.size && !startsAt cs j s do
    j := j + 1
  return j

/-- The value of attribute `name` in the text of a tag, if it has one. -/
def attribute? (tag : String) (name : String) : Option String := do
  let key := s!" {name}=\""
  let rest ← (tag.splitOn key)[1]?
  (rest.splitOn "\"")[0]?

/-- What a page's prose cites: each citation, and the link around it, if any. -/
structure Cited where
  citation : Citation
  href : Option String

/-- The citations in the prose of the HTML page `html`. -/
def citedInPage (html : String) : Array Cited := Id.run do
  let cs := html.toList.toArray
  let mut out := #[]
  let mut i := 0
  let mut inMain := false
  let mut skip := 0
  let mut links : List (Option String) := []
  let mut textStart := 0
  while i < cs.size do
    if cs[i]! != '<' then
      i := i + 1
      continue
    if inMain && skip == 0 then
      for c in citationsIn (cs.extract textStart i) do
        out := out.push { citation := c, href := links.head?.join }
    if startsAt cs i "<!--" then
      i := findFrom cs i "-->" + 3
      textStart := i
      continue
    let close := cs[i + 1]? == some '/'
    let nameStart := if close then i + 2 else i + 1
    let mut j := nameStart
    while cs[j]?.any Char.isAlphanum do
      j := j + 1
    let name := (String.ofList (cs.extract nameStart j).toList).toLower
    let mut quote : Option Char := none
    while j < cs.size && (quote.isSome || cs[j]! != '>') do
      let c := cs[j]!
      if quote == some c then quote := none
      else if quote.isNone && (c == '"' || c == '\'') then quote := some c
      j := j + 1
    let tag := String.ofList (cs.extract i j).toList
    i := j + 1
    if !close && (name == "script" || name == "style") then
      i := findFrom cs i s!"</{name}>"
    else if name == "main" then
      inMain := !close
    else if name == "a" then
      links := if close then links.drop 1 else attribute? tag "href" :: links
    else if skipped.contains name then
      skip := if close then skip - 1 else skip + 1
    textStart := i
  return out

/--
The address of every page of the site in `dir`, such as `/adrs/`, from the
`xref.json` that Verso writes there. Pages left in `dir` by an earlier build
are not among them.
-/
def pageAddresses (dir : System.FilePath) : IO (Except String (Array String)) := do
  let text ← IO.FS.readFile (dir / "xref.json")
  return do
    let json ← Lean.Json.parse text
    let sections ← (← json.getObjVal? "Verso.Genre.Manual.section").getObjVal? "contents"
    let mut out := #[]
    for (_, targets) in (← sections.getObj?).toList do
      for target in ← targets.getArr? do
        let address ← (← target.getObjVal? "address").getStr?
        unless out.contains address do
          out := out.push address
    return out.qsort (· < ·)

/--
One message per problem with the rendered site in `dir`, the `html-multi`
output: an ADR without a page, or a citation in prose that is not a link to
its ADR's page.
-/
def checkRendered (dir : System.FilePath) (ids : Array String) : IO (Array String) := do
  let addresses ← match ← pageAddresses dir with
    | .ok addresses => pure addresses
    | .error e => return #[s!"{dir / "xref.json"}: {e}"]
  let mut errors := #[]
  for id in ids do
    unless addresses.contains s!"/adrs/ADR-{id}/" do
      errors := errors.push s!"{dir}: ADR-{id} has no page at adrs/ADR-{id}/"
  for address in addresses do
    let page := (address.splitOn "/").foldl (fun p c => if c.isEmpty then p else p / c) dir / "index.html"
    for cited in citedInPage (← IO.FS.readFile page) do
      let c := cited.citation
      unless cited.href == some (adrHref c.id) do
        errors := errors.push s!"{page}: {c.text} is not a link to {adrHref c.id}"
  return errors

end FirSpecSite
