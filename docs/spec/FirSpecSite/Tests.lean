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

/-! Citations end at the last digit of the id, and only ids of four or six digits are well formed. -/

#guard (citations "see ADR-2026-10-30-1031.").map (·.id) == #["2026-10-30-1031"]
#guard (citations "see ADR-2026-10-30-103112.").map (·.id) == #["2026-10-30-103112"]
#guard (citations "ADR-2026-10-30-1031, ADR-2026-10-30-1046").map (·.start) == #[0, 21]
#guard (citations "ADR-2026-10-30-10311").map (·.wellFormed) == #[false]
#guard (citations "ADR-2026-10-30-1031123").map (·.wellFormed) == #[false]
#guard (citations "ADR-YYYY-MM-DD-HHMM and ADR-… and ADR-2026-10-30-").isEmpty
#guard (citations "(S1, ADR-2026-10-29-2006; ADR-2026-10-29-2017)").map (·.text) ==
  #["ADR-2026-10-29-2006", "ADR-2026-10-29-2017"]

#guard segments "see ADR-2026-10-29-2015." ==
  #[.text "see ", .cite ⟨4, 23, "2026-10-29-2015", true⟩, .text "."]
#guard segments "ADR-2026-10-29-2015" == #[.cite ⟨0, 19, "2026-10-29-2015", true⟩]

#guard adrIdOfFileName? "2026-10-29-2015-literate-lean-spec.md" == some "2026-10-29-2015"
#guard adrIdOfFileName? "2026-10-30-103112-adr.md" == some "2026-10-30-103112"
#guard adrIdOfFileName? "2026-10-30-10311-adr.md" == none
#guard adrIdOfFileName? "README.md" == none

/-! Code is quoted, not cited. -/

private def prose (s : String) : Array String :=
  (citationsIn (blankCode s.toList.toArray)).map (·.text)

#guard prose "`ADR-2026-10-30-103112` and ADR-2026-10-30-1031" == #["ADR-2026-10-30-1031"]
#guard prose "``a ` ADR-2026-10-30-1031`` ADR-2026-10-30-1046" == #["ADR-2026-10-30-1046"]
#guard prose "an unclosed ` ADR-2026-10-30-1031" == #["ADR-2026-10-30-1031"]
#guard prose "x\n```\nADR-2026-10-30-1031\n```\nADR-2026-10-30-1046" == #["ADR-2026-10-30-1046"]

/-! The check of the sources locates each citation that names no ADR. -/

private def known : String → Bool := (#["2026-10-29-2015"].contains ·)

#guard checkText known "a.md" "ok ADR-2026-10-29-2015\n  ADR-2026-10-29-2099 `ADR-2026-10-29-2098`" ==
  #["a.md:2:3: ADR-2026-10-29-2099 names no ADR in docs/adrs/"]
#guard checkText known "a.lean" "ADR-2026-10-29-20150" ==
  #["a.lean:1:1: ADR-2026-10-29-20150 is not an ADR id, which ends in HHMM or HHMMSS"]

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
#guard ((linked #[.link #[.text "ADR-2026-10-29-2099"] "https://example.com"]).map (·.size)) ==
  .ok 1
#guard (linked #[.text "ADR-2026-10-29-2099"]).toOption.isNone
#guard (match linked #[.text "ADR-2026-10-29-2099"] with
  | .error e => e == #["here: ADR-2026-10-29-2099 names no ADR in docs/adrs/"]
  | .ok _ => false)

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

private def parsed := parseAdr ctx "2026-10-30-0000" fixture

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

#guard (parseAdr ctx "x" "No heading\n").toOption.isNone
#guard (parseAdr ctx "x" "# Title\n\nNo status\n").toOption.isNone
#guard (parseAdr ctx "x" "# T\n\nStatus: accepted\n\n<div>raw</div>\n").toOption.isNone
#guard (parseAdr ctx "x" "# T\n\nStatus: accepted\n\n![an image](a.png)\n").toOption.isNone
#guard (parseAdr ctx "x" "# T\n\nStatus: accepted\n\n[up](../../../x)\n").toOption.isNone
#guard (parseAdr ctx "x" "# T\n\nStatus: accepted\n\na\\\nb\n").toOption.isNone
#guard (parseAdr ctx "x" "# T\n\nStatus: accepted\n\n~~gone~~\n").toOption.isNone
#guard (parseAdr ctx "x" "# T\n\nStatus: accepted\n\n- [x] done\n").toOption.isNone
#guard (parseAdr ctx "x" "# T\n\nStatus: accepted\n\n---\n").toOption.isNone
#guard (parseAdr ctx "x" "# T\n\nStatus: accepted\n\n&frac12;\n").toOption.isNone
#guard (parseAdr ctx "x" "# T\n\nStatus: accepted\n\n&#x2192; &#8594;\n").map
  (·.1.part.content) == .ok #[.para #[.text "Status: accepted"], .para #[.text "\u2192 \u2192"]]
#guard (parseAdr ctx "x" "# T\n\nStatus: accepted\n\nsee www.example.com\n").map
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
