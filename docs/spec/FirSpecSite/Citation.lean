/-!
ADR ids and citations (ADR-2026-10-30-1329). An ADR's id is the timestamp
that starts its file name, `YYYY-MM-DD-HHMM` or `YYYY-MM-DD-HHMMSS`, and a
citation is `ADR-` followed by an id. A citation ends with the last digit of
its run, so `ADR-2026-10-30-1031` never matches the start of
`ADR-2026-10-30-103112`. Placeholders such as `ADR-YYYY-MM-DD-HHMM` are not
citations.
-/

namespace FirSpecSite

/-- One `ADR-…` citation in a text, by character positions. -/
structure Citation where
  /-- The position of the `A` of `ADR-`. -/
  start : Nat
  /-- The position just after the last digit. -/
  stop : Nat
  /-- What follows `ADR-`, such as `2026-10-29-2015`. -/
  id : String
  /-- Whether the time has the four or six digits of an id. -/
  wellFormed : Bool
deriving Repr, BEq, Inhabited

/-- The text of the citation, such as `ADR-2026-10-29-2015`. -/
def Citation.text (c : Citation) : String := "ADR-" ++ c.id

private def digitsAt (cs : Array Char) (i n : Nat) : Bool :=
  (List.range n).all fun k => cs[i + k]?.any Char.isDigit

private def charAt (cs : Array Char) (i : Nat) (c : Char) : Bool :=
  cs[i]? == some c

private def digitRun (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut n := 0
  while cs[i + n]?.any Char.isDigit do
    n := n + 1
  return n

/--
The citation that starts at `i`, if any: `ADR-`, a date `YYYY-MM-DD-` and a run
of digits. The run must have four or six digits for the citation to be well
formed; any other length is a malformed citation.
-/
def citationAt? (cs : Array Char) (i : Nat) : Option Citation := do
  guard <| charAt cs i 'A' && charAt cs (i + 1) 'D' && charAt cs (i + 2) 'R' && charAt cs (i + 3) '-'
  let d := i + 4
  guard <| digitsAt cs d 4 && charAt cs (d + 4) '-' && digitsAt cs (d + 5) 2 &&
    charAt cs (d + 7) '-' && digitsAt cs (d + 8) 2 && charAt cs (d + 10) '-'
  let run := digitRun cs (d + 11)
  guard (run > 0)
  let stop := d + 11 + run
  let id := String.ofList (cs.extract d stop).toList
  return { start := i, stop, id, wellFormed := run == 4 || run == 6 }

/-- Every citation in `cs`, in order. Citations do not overlap. -/
def citationsIn (cs : Array Char) : Array Citation := Id.run do
  let mut out := #[]
  let mut i := 0
  while i < cs.size do
    match citationAt? cs i with
    | some c =>
      out := out.push c
      i := c.stop
    | none => i := i + 1
  return out

/-- Every citation in `s`, in order. -/
def citations (s : String) : Array Citation := citationsIn s.toList.toArray

/-- A piece of a text: plain text, or a citation. -/
inductive Segment where
  | text (s : String)
  | cite (c : Citation)
deriving Repr, BEq, Inhabited

/-- Splits `s` into plain text and citations, dropping empty text. -/
def segments (s : String) : Array Segment := Id.run do
  let cs := s.toList.toArray
  let mut out := #[]
  let mut last := 0
  for c in citationsIn cs do
    if c.start > last then
      out := out.push (.text (String.ofList (cs.extract last c.start).toList))
    out := out.push (.cite c)
    last := c.stop
  if last < cs.size then
    out := out.push (.text (String.ofList (cs.extract last cs.size).toList))
  return out

/--
The id at the start of an ADR's file name, `YYYY-MM-DD-HHMM-slug.md` or
`YYYY-MM-DD-HHMMSS-slug.md`. The `adr-ids` hook checks the rest of the name.
-/
def adrIdOfFileName? (name : String) : Option String := do
  let cs := name.toList.toArray
  guard <| name.endsWith ".md"
  guard <| digitsAt cs 0 4 && charAt cs 4 '-' && digitsAt cs 5 2 && charAt cs 7 '-' &&
    digitsAt cs 8 2 && charAt cs 10 '-'
  let run := digitRun cs 11
  guard <| (run == 4 || run == 6) && charAt cs (11 + run) '-'
  return String.ofList (cs.extract 0 (11 + run)).toList

private def runLength (cs : Array Char) (i : Nat) (c : Char) : Nat := Id.run do
  let mut n := 0
  while cs[i + n]? == some c do
    n := n + 1
  return n

/--
`line` with each code span, from a run of backticks to the next run of the same
length, blanked out.
-/
def blankCodeSpans (line : Array Char) : Array Char := Id.run do
  let mut out := line
  let mut i := 0
  while i < line.size do
    if line[i]! != '`' then
      i := i + 1
      continue
    let n := runLength line i '`'
    let mut j := i + n
    let mut close := none
    while j < line.size && close.isNone do
      if line[j]! == '`' then
        let m := runLength line j '`'
        if m == n then close := some (j + m)
        j := j + m
      else j := j + 1
    match close with
    | some stop =>
      for k in [i:stop] do
        out := out.set! k ' '
      i := stop
    | none => i := i + n
  return out

private def isFence (line : Array Char) : Bool :=
  let rest := line.toList.dropWhile (· == ' ')
  rest.take 3 == ['`', '`', '`'] || rest.take 3 == ['~', '~', '~']

/--
`cs` with its code blanked out: code spans, and fenced code blocks with their
fences. Line breaks stay, so positions do not move. A citation in code is
quoted, not cited.
-/
def blankCode (cs : Array Char) : Array Char := Id.run do
  let mut out := #[]
  let mut inFence := false
  let mut start := 0
  for i in [0:cs.size + 1] do
    unless i == cs.size || cs[i]! == '\n' do continue
    let line := cs.extract start i
    if isFence line then
      inFence := !inFence
      out := out ++ line.map fun _ => ' '
    else if inFence then
      out := out ++ line.map fun _ => ' '
    else
      out := out ++ blankCodeSpans line
    if i < cs.size then out := out.push '\n'
    start := i + 1
  return out

/-- The 1-based line and column of the character at `pos` in `cs`. -/
def lineColumn (cs : Array Char) (pos : Nat) : Nat × Nat := Id.run do
  let mut line := 1
  let mut col := 1
  for c in cs.extract 0 pos do
    if c == '\n' then
      line := line + 1
      col := 1
    else
      col := col + 1
  return (line, col)

end FirSpecSite
