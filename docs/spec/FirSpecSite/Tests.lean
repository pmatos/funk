import FirSpecSite

/-!
Tests of the ADR appendix and of citation links. They run when the
`FirSpecSite` library builds, so `scripts/build-spec.sh` runs them.
-/

namespace FirSpecSite.Tests

open Verso.Genre Manual

private instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

/-!
The citation grammar and the check of a text pass every case of `citation-cases.json`, which
the `adr-citations` hook's tests also read, so the two definitions cannot drift
(ADR-2026-11-05-1709). Lake rebuilds this module when the table changes.
-/

private def caseTable : String := include_str "citation-cases.json"

/-- One line per case of the table that the grammar or the check gets wrong. -/
private def caseFailures : Except String (Array String) := do
  let table ← Lean.Json.parse caseTable
  let known ← table.getObjValAs? (Array String) "known"
  let mut out := #[]
  for entry in ← table.getObjValAs? (Array Lean.Json) "cases" do
    let text ← entry.getObjValAs? String "text"
    let cites ← entry.getObjValAs? (Array String) "citations"
    let errors ← entry.getObjValAs? (Array String) "errors"
    let cs := text.toList.toArray
    let found := (citationsIn (blankCode cs)).map fun c =>
      let (line, col) := lineColumn cs c.start
      s!"{line}:{col} {c.text}"
    unless found == cites do
      out := out.push s!"{text.quote}: citations {found}, expected {cites}"
    let got := checkText (known.contains ·) "a.md" text
    unless got == errors do
      out := out.push s!"{text.quote}: errors {got}, expected {errors}"
  return out

#eval show IO Unit from do
  let failures ← IO.ofExcept caseFailures
  unless failures.isEmpty do
    throw <| IO.userError ("citation-cases.json:\n" ++ "\n".intercalate failures.toList)

#guard (citations "ADR-2026-10-30-1031, ADR-2026-10-30-1046").map (·.start) == #[0, 21]

#guard segments "see ADR-2026-10-29-2015." ==
  #[.text "see ", .cite ⟨4, 23, "2026-10-29-2015", true⟩, .text "."]
#guard segments "ADR-2026-10-29-2015" == #[.cite ⟨0, 19, "2026-10-29-2015", true⟩]

#guard adrIdOfFileName? "2026-10-29-2015-literate-lean-spec.md" == some "2026-10-29-2015"
#guard adrIdOfFileName? "2026-10-30-103112-adr.md" == some "2026-10-30-103112"
#guard adrIdOfFileName? "2026-10-30-10311-adr.md" == none
#guard adrIdOfFileName? "README.md" == none

/-! The linking tests below know one ADR. -/

private def known : String → Bool := (#["2026-10-29-2015"].contains ·)

/-! Linking turns each citation into a cross-reference to the ADR's tag. -/

private partial def refs : Inl → Array String
  | .other c xs =>
    match c.data.getObjValAs? String "canonicalName" with
    | .ok name => #[name]
    | .error _ => xs.flatMap refs
  | .emph xs | .bold xs | .concat xs => xs.flatMap refs
  | _ => #[]

private def linked (xs : Array Inl) : Except (Array String) (Array Inl) :=
  match (linkInlines known "here" xs).run #[] with
  | (ys, #[]) => .ok ys
  | (_, errors) => .error errors

#guard ((linked #[.text "see ADR-2026-10-29-", .text "2015 and ", .code "ADR-2026-10-29-2099"]).map
  (·.flatMap refs)) == .ok #["ADR-2026-10-29-2015"]
#guard ((linked #[.emph #[.text "ADR-2026-10-29-2015"]]).map (·.flatMap refs)) ==
  .ok #["ADR-2026-10-29-2015"]

/-! A citation in the text of a link, or in a heading, cannot link to its ADR, so it is an error. -/

private def inLink (cited target : String) : String :=
  s!"here: {cited} is the text of a link to {target}; cite the ADR as plain text outside the link"

#guard ((linked #[.link #[.text "a ", .code "ADR-2026-10-29-2015"] "https://example.com"]).map
  (·.size)) == .ok 1
#guard linked #[.link #[.emph #[.text "ADR-2026-10-29-2015"]] "https://example.com"] ==
  .error #[inLink "ADR-2026-10-29-2015" "https://example.com"]
#guard ((linked #[adrRef "2026-10-29-2015" #[.text "ADR-2026-10-29-2015"]]).map (·.flatMap refs)) ==
  .ok #["ADR-2026-10-29-2015"]
#guard linked #[adrRef "2026-10-29-2016" #[.text "ADR-2026-10-29-2015"]] ==
  .error #[inLink "ADR-2026-10-29-2015" "ADR-2026-10-29-2016"]
#guard (linked #[.text "ADR-2026-10-29-2099"]).toOption.isNone
#guard (match linked #[.text "ADR-2026-10-29-2099"] with
  | .error e => e == #["here: ADR-2026-10-29-2099 names no ADR in docs/adrs/"]
  | .ok _ => false)

private def mkPart (title : String) (tag : Option String := none) (content : Array Blk := #[])
    (subParts : Array Prt := #[]) : Prt :=
  { title := #[.text title], titleString := title, metadata := some { tag }, content, subParts }

private def partErrors (doc : Prt) : Array String :=
  let fileOf (tag : String) := if tag == "ADR-2026-10-29-2015" then some "docs/adrs/a.md" else none
  ((linkPart known fileOf {} doc).run #[]).2

private def inHeading (place cited : String) : String :=
  s!"{place}: {cited} is in a heading, where it cannot be a link; cite it in the text below"

#guard partErrors (mkPart "Doc" none #[] #[mkPart "Sec ADR-2026-10-29-2015"]) ==
  #[inHeading "in “Doc › Sec ADR-2026-10-29-2015”" "ADR-2026-10-29-2015"]
#guard partErrors (mkPart "Doc" none #[] #[{ mkPart "Sec" with title := #[.code "ADR-2026-10-29-2099"] }]) ==
  #[]
#guard partErrors (mkPart "Doc" none #[] #[mkPart "ADR-2026-10-29-2015: x" "ADR-2026-10-29-2015"
    #[.para #[.link #[.text "ADR-2026-10-29-2015"] "u"]] #[mkPart "On ADR-2026-10-29-2015"]]) ==
  #["docs/adrs/a.md: ADR-2026-10-29-2015 is the text of a link to u; cite the ADR as plain text outside the link",
    inHeading "docs/adrs/a.md, in “On ADR-2026-10-29-2015”" "ADR-2026-10-29-2015"]

/-! An ADR's Markdown keeps its headings, lists, code, tables and links. -/

private def fixture : String := "# Use a fixture

Status: accepted; refined by ADR-2026-10-29-2015

## Context

Some *emphasis*, `code`, <https://example.com> and a [spike](../spikes/leanmlir.md#top).

- one
- two

```sh
echo 1 &amp; 2
```

| a | b |
| - | - |
| 1 | [an ADR](2026-10-29-2015-literate-lean-spec.md) |

### Detail

AT&T &amp; more.

## Decision

1. first
"

private def ctx : MdContext := { adrIds := #[("2026-10-29-2015-literate-lean-spec.md", "2026-10-29-2015")] }

private def parsed := parseAdr ctx "a.md" "2026-10-30-0000" fixture

private def kind : Blk → String
  | .para _ => "p" | .ul _ => "ul" | .ol .. => "ol" | .code _ => "code"
  | .other c _ => c.name.toString | _ => "other"

#guard (parsed.map fun (a, _) => a.part.titleString) == .ok "ADR-2026-10-30-0000: Use a fixture"
#guard (parsed.map fun (a, _) => (a.status.flatMap refs, a.status.size)) == .ok (#[], 1)
#guard (parsed.map fun (a, _) => a.part.subParts.map (·.titleString)) == .ok #["Context", "Decision"]
#guard (parsed.map fun (a, _) => a.part.subParts.map (·.subParts.map (·.titleString))) ==
  .ok #[#["Detail"], #[]]
#guard (parsed.map fun (a, _) => a.part.subParts[0]!.content.map kind) ==
  .ok #["p", "ul", "code", "Verso.Genre.Manual.Block.table"]
#guard (parsed.map fun (_, links) => links) == .ok #["docs/spikes/leanmlir.md"]
#guard (parsed.map fun (a, _) => a.part.metadata.bind (·.tag)) == .ok (some "ADR-2026-10-30-0000")

private partial def inlinesOf : Blk → Array Inl
  | .para xs => xs
  | .other _ bs | .blockquote bs => bs.flatMap inlinesOf
  | .ul items | .ol _ items => items.flatMap fun ⟨bs⟩ => bs.flatMap inlinesOf
  | _ => #[]

private partial def urls : Inl → Array String
  | .link _ url => #[url]
  | .emph xs | .bold xs | .concat xs => xs.flatMap urls
  | _ => #[]

#guard (parsed.map fun (a, _) => (a.part.subParts[0]!.content.flatMap inlinesOf).flatMap urls) ==
  .ok #["https://example.com",
    "https://github.com/pmatos/funk/blob/main/docs/spikes/leanmlir.md#top"]
#guard (parsed.map fun (a, _) => (a.part.subParts[0]!.content.flatMap inlinesOf).flatMap refs) ==
  .ok #["ADR-2026-10-29-2015"]
#guard (parsed.map fun (a, _) => a.part.subParts[0]!.content[2]!) == .ok (.code "echo 1 &amp; 2\n")
#guard (parsed.map fun (a, _) => a.part.subParts[0]!.subParts[0]!.content) ==
  .ok #[.para #[.text "AT&T & more."]]

#guard (parseAdr ctx "a.md" "x" "No heading\n").toOption.isNone
#guard (parseAdr ctx "a.md" "x" "# Title\n\nNo status\n").toOption.isNone
#guard (parseAdr ctx "a.md" "x" "# T\n\nStatus: accepted\n\n<div>raw</div>\n").toOption.isNone
#guard (parseAdr ctx "a.md" "x" "# T\n\nStatus: accepted\n\n![an image](a.png)\n").toOption.isNone
#guard (parseAdr ctx "a.md" "x" "# T\n\nStatus: accepted\n\n[up](../../../x)\n").toOption.isNone
#guard (parseAdr ctx "a.md" "x" "# T\n\nStatus: accepted\n\na\\\nb\n").toOption.isNone
#guard (parseAdr ctx "a.md" "x" "# T\n\nStatus: accepted\n\n~~gone~~\n").toOption.isNone
#guard (parseAdr ctx "a.md" "x" "# T\n\nStatus: accepted\n\n- [x] done\n").toOption.isNone
#guard (parseAdr ctx "a.md" "x" "# T\n\nStatus: accepted\n\n---\n").toOption.isNone
#guard (parseAdr ctx "a.md" "x" "# T\n\nStatus: accepted\n\n&frac12;\n").toOption.isNone
#guard (parseAdr ctx "a.md" "x" "# T\n\nStatus: accepted\n\n&#x2192; &#8594;\n").map
  (·.1.part.content) == .ok #[.para #[.text "Status: accepted"], .para #[.text "\u2192 \u2192"]]
#guard (parseAdr ctx "a.md" "x" "# T\n\nStatus: accepted\n\nsee www.example.com\n").map
  (fun (a, _) => (a.part.content.flatMap inlinesOf).flatMap urls) == .ok #["http://www.example.com"]

/-! The check of the rendered pages reads prose only. -/

private def page : String :=
  "<head><title>ADR-2026-10-29-2016</title></head><main><h1>ADR-2026-10-29-2016: x</h1>" ++
  "<p>see <a class=\"x\" href=\"adrs/ADR-2026-10-29-2015/#ADR-2026-10-29-2015\">ADR-2026-10-29-2015</a>" ++
  " and ADR-2026-10-29-2017 <code>ADR-2026-10-29-2018</code></p>" ++
  "<script>if (a <b) { x = '</p>ADR-2026-10-29-2019' }</script><!-- ADR-2026-10-29-2020 -->" ++
  "<nav><a href=\"\">ADR-2026-10-29-2021</a></nav></main><p>ADR-2026-10-29-2022</p>"

#guard (citedInPage page).map (fun c => (c.citation.id, c.href)) ==
  #[("2026-10-29-2015", some "adrs/ADR-2026-10-29-2015/#ADR-2026-10-29-2015"), ("2026-10-29-2017", none)]
#guard attribute? "<a class=\"x\" href=\"y\">" "href" == some "y"

end FirSpecSite.Tests
