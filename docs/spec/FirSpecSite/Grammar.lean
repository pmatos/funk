/-!
The text of a grammar box (ADR-2026-11-05-2012). Its first line is the
nonterminal, in LaTeX. Each further line is one alternative: the
constructors it shows, then its notation in LaTeX, after a space. The
constructors are short names separated by commas, or `-` for a line that
shows none, such as `\dots`. Blank lines are skipped.

```
\mathit{pred}
eq,ne              \mathsf{eq} \mid \mathsf{ne}
slt,sle,sgt,sge    \mathsf{slt} \mid \mathsf{sle} \mid \mathsf{sgt} \mid \mathsf{sge}
```

The box shows the alternatives in a LaTeX `array`, one per row, with `::=`
before the first and `|` before the others, as the WebAssembly specification
writes its grammar.
-/

namespace FirSpecSite

/-- One alternative of a grammar box. -/
structure GrammarLine where
  /-- The short names of the constructors it shows. -/
  tags : Array String
  /-- Its notation, in LaTeX. -/
  latex : String
deriving BEq, Repr

/-- A grammar box: its nonterminal and its alternatives. -/
structure Grammar where
  nonterminal : String
  lines : Array GrammarLine
deriving BEq, Repr

/-- Parses the text of a grammar box. -/
def parseGrammar (src : String) : Except String Grammar := do
  let lines := (src.splitOn "\n").map (·.trimAscii.copy) |>.filter (!·.isEmpty)
  let nt :: alts := lines
    | throw "a grammar box needs a nonterminal on its first line"
  if alts.isEmpty then throw s!"the grammar of {nt} has no alternatives"
  let parsed ← alts.toArray.mapM fun line => do
    let (tag, rest) := line.toList.span (!·.isWhitespace)
    let latex := (String.ofList rest).trimAscii.copy
    if latex.isEmpty then
      throw s!"the line '{line}' has no notation after its constructors"
    let tag := String.ofList tag
    let tags := if tag == "-" then #[] else (tag.splitOn ",").toArray
    if tags.any (·.isEmpty) then
      throw s!"the line '{line}' has an empty constructor name"
    return { tags, latex : GrammarLine }
  return { nonterminal := nt, lines := parsed }

private instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

/-- The LaTeX of a grammar box. -/
def Grammar.toLatex (g : Grammar) : String :=
  let rows := g.lines.toList.zipIdx.map fun (l, i) =>
    (if i == 0 then s!"{g.nonterminal} & ::= & " else "& \\mid & ") ++ l.latex
  "\\begin{array}{rcl}\n" ++ " \\\\\n".intercalate rows ++ "\n\\end{array}"

#guard parseGrammar "\\mathit{p}\n  eq,ne  \\mathsf{eq} \\mid \\mathsf{ne}\n\n  -  \\dots\n" ==
  .ok { nonterminal := "\\mathit{p}",
        lines := #[{ tags := #["eq", "ne"], latex := "\\mathsf{eq} \\mid \\mathsf{ne}" },
                   { tags := #[], latex := "\\dots" }] }
#guard (parseGrammar "\\mathit{p}\n  eq").toOption.isNone
#guard (parseGrammar "\\mathit{p}").toOption.isNone
#guard (parseGrammar "\\mathit{p}\n  eq,,ne  x").toOption.isNone
#guard ((parseGrammar "x\n a  A\n b  B").map Grammar.toLatex) ==
  .ok "\\begin{array}{rcl}\nx & ::= & A \\\\\n& \\mid & B\n\\end{array}"

end FirSpecSite
