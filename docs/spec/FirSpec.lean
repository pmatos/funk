import VersoManual
import Fir

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "The fir specification" =>

fir is the intermediate representation of funk, a compiler toolchain in the
spirit of LLVM. This document is fir's specification, version 0. It covers
the M0 core: integers of any width, arithmetic, bitwise ops and shifts,
comparisons, width changes, `freeze`, branches with block arguments, calls
and return.

The specification is literate Lean (ADR-2026-10-29-2015). Its formal content
is the Lean definitions of the package `fir` in the repository's `lean/`
directory, and the prose beside them explains them. This document renders
both from the same source on every change, so the readable specification
cannot drift from the formal one. Where the two seem to disagree, the Lean
definitions are normative.

The chapters follow the WebAssembly specification:

* _Abstract syntax_ gives the terms of fir: dialects, types, ops, blocks,
  functions, modules and locations, and the ops of the core dialect.
* _Validation_ gives the rules that decide which terms are fir programs.
* _Execution_ explains poison and immediate UB in plain words, then gives
  what a run can end with, what a function shows to an observer, the
  refinement relation that defines correctness, and how each op treats
  poison.
* _Text format_ gives fir's one canonical text: its tokens, its grammar,
  the printer that fixes its layout, the round-trip properties, and the
  parser.

fir is built from dialects, so that it can reach any kind of hardware
(ADR-2026-10-29-2016). Every definition below is written once for every
dialect, and the core dialect of M0 is its first instance. The rules of each
op family, for validation and execution, are added by the tickets that build
the family. The decisions behind the definitions are architecture decision
records (ADRs), cited by their ids, such as ADR-2026-10-29-2014. Each
citation links to the ADR in the appendix, which holds every ADR.

# Abstract syntax

The abstract syntax is parameterized over the dialect. A dialect supplies its
op instances and its types; a module of any dialect is made of the same
functions, blocks and ops.

{includeLiterate "." Fir.Syntax.Dialect "Dialects" (level := 2)}

{includeLiterate "." Fir.Syntax.Location "Locations" (level := 2)}

{includeLiterate "." Fir.Syntax.Module "Modules, functions, blocks and ops" (level := 2)}

{includeLiterate "." Fir.Core.Types "Core types" (level := 2)}

{includeLiterate "." Fir.Core.Ops "Core ops" (level := 2)}

{includeLiterate "." Fir.Core.Signature "Core signatures" (level := 2)}

# Validation

{includeLiterate "." Fir.Validation.Scope "Scope and symbols" (level := 2)}

{includeLiterate "." Fir.Validation.Dominance "Dominance" (level := 2)}

{includeLiterate "." Fir.Validation.Rules "The general rules" (level := 2)}

{includeLiterate "." Fir.Core.Validation "Core rules" (level := 2)}

{includeLiterate "." Fir.Core.Rejects "A rejected function" (level := 2)}

# Execution

{includeLiterate "." Fir.Execution.Values "Values and refinement" (level := 2)}

{includeLiterate "." Fir.Execution.PoisonUB "Poison and immediate UB" (level := 2)}

{includeLiterate "." Fir.Execution.Effects "Effects and op semantics" (level := 2)}

{includeLiterate "." Fir.Execution.Behaviour "Outcomes and behaviours" (level := 2)}

{includeLiterate "." Fir.Execution.Fuel "Fuel and progress" (level := 2)}

{includeLiterate "." Fir.Execution.Refinement "Refinement" (level := 2)}

{includeLiterate "." Fir.Execution.Propagation "Poison classes" (level := 2)}

{includeLiterate "." Fir.Core.Values "Core values" (level := 2)}

{includeLiterate "." Fir.Core.Poison "Core poison classes" (level := 2)}

{includeLiterate "." Fir.Core.Unlawful "Semantics the obligations reject" (level := 2)}

# Text format

{includeLiterate "." Fir.Text.Lexical "Tokens" (level := 2)}

{includeLiterate "." Fir.Text.Grammar "Grammar" (level := 2)}

{includeLiterate "." Fir.Core.Text "The core dialect in text" (level := 2)}

{includeLiterate "." Fir.Text.Print "The canonical printer" (level := 2)}

{includeLiterate "." Fir.Text.RoundTrip "Round trips" (level := 2)}

{includeLiterate "." Fir.Text.Lex "The parser" (level := 2)}

{includeLiterate "." Fir.Text.Read "Reading the grammar" (level := 2)}

{includeLiterate "." Fir.Text.ReadLocs "Reading the location table and the module" (level := 2)}

{includeLiterate "." Fir.Text.Decode "Decoding" (level := 2)}

{includeLiterate "." Fir.Text.Example "Example" (level := 2)}

# Architecture decision records
%%%
tag := "adrs"
file := "adrs"
number := false
htmlToc := false
%%%

An architecture decision record, or ADR, records one decision about fir or
funk: what was decided, why, and what it costs. This appendix holds every
ADR in the repository's `docs/adrs/` directory, one page each, rendered from
its Markdown file when this document is built, so it matches the commit
named at the foot of each page.

An ADR's id is the UTC time it was written, and the spec and the ADRs cite
it as `ADR-` followed by the id, such as ADR-2026-10-30-1329, which also says
how ids stay unique. Every citation links to the ADR's page. An accepted
ADR is not rewritten: a later ADR refines or supersedes it, and its status
names the later one.
