import VersoManual
import Fir
import FirSpecSite.ReadableElab
import FirSpec.Syntax.Dialect
import FirSpec.Syntax.Location
import FirSpec.Syntax.Module
import FirSpec.Core.Types
import FirSpec.Core.Ops
import FirSpec.Core.Signature
import FirSpec.Execution.CallSteps
import FirSpec.Validation.Scope
import FirSpec.Validation.Dominance
import FirSpec.Validation.Rules
import FirSpec.Core.Validation
import FirSpec.Core.Rejects
import FirSpec.Validation.Check
import FirSpec.Validation.Tables
import FirSpec.Validation.Search
import FirSpec.Validation.Graph
import FirSpec.Validation.CheckOps
import FirSpec.Validation.CheckFuncs
import FirSpec.Validation.CheckModule
import FirSpec.Core.Check

open Verso.Genre Manual
open FirSpecSite

set_option pp.rawOnError true

#doc (Manual) "The fir specification" =>

fir is the intermediate representation of funk, a compiler toolchain in the
spirit of LLVM. This document is fir's specification, version 0. It covers
the M0 core: integers of any width from 1 to 16,777,215, arithmetic,
bitwise ops and shifts, comparison and selection, width changes, `freeze`
and the constant `poison`, branches with block arguments, calls and
return.

The specification is literate Lean (ADR-2026-10-29-2015). Its formal content
is the Lean definitions of the package `fir` in the repository's `lean/`
directory, and the prose beside them explains them. This document renders
both from the same source on every change, so the readable specification
cannot drift from the formal one. Where the two seem to disagree, the Lean
definitions are normative.

Some sections show each Lean declaration as a readable block: what it says,
in words and in mathematical notation, in the style of the WebAssembly
specification. The Lean, with its statements and proofs, is hidden under
each block and opens with a click. The build checks every block against the
Lean it explains, and fails when the Lean changes under it
(ADR-2026-11-05-2012).

Readable blocks use the notation of the WebAssembly specification.
$`A ::= B \mid C` gives the alternatives of $`A`, one per row of a grammar
box, and a box whose first alternative is $`\dots` continues the
alternatives of the boxes above it. $`A^?` is an optional $`A`, and $`A^*`
a possibly empty sequence of $`A`. A subscript, as in $`\mathsf{add}_N`,
gives the width in bits of the integers that an op works on, and
$`\mathsf{i}N` is the type of $`N`-bit integers. $`\epsilon` is the empty
sequence, and $`|s|` the length of the sequence $`s`.

Validation, as in the WebAssembly specification, is written with inference
rules. A rule $`\frac{P_1 \quad \dots \quad P_n}{J}` says that when its
premises $`P_1, \dots, P_n`, above the line, hold, its conclusion $`J`,
below the line, holds; a rule with no premise holds outright. A relation
given by rules is the least one that they close. A judgement such as
$`C \vdash f~\text{valid}` says that $`f` is valid in the context $`C`.

The chapters follow the WebAssembly specification:

* _Abstract syntax_ gives the terms of fir: dialects, types, ops, blocks,
  functions, modules and locations, and the ops of the core dialect.
* _Validation_ gives the rules that decide which terms are fir programs,
  and the check that decides them, which `fir-ref validate` runs.
* _Execution_ explains poison and immediate UB in plain words, then gives
  what a run can end with, what a function shows to an observer, the
  refinement relation that defines correctness, and how each op treats
  poison. It then gives the interpreter, the execution rules of every
  core op with the proofs that they meet the poison obligations, the
  exhaustive, scripted and sampled modes that `fir-ref run` walks, and
  the proofs about runs: fuel monotonicity, progress, no stuck path, and
  refinement through calls.
* _Text format_ gives fir's one canonical text: its tokens, its grammar,
  the printer that fixes its layout, the round-trip properties, and the
  parser, with the proofs that parsing a printed well-formed module gives
  it back and that every module the parser gives is well formed.

fir is built from dialects, so that it can reach any kind of hardware
(ADR-2026-10-29-2016). Every definition below is written once for every
dialect, and the core dialect of M0 is its first instance. Each op family
of the core dialect has its execution rules, and the proofs of its
obligations, in sections of their own. The decisions behind the
definitions are architecture decision records (ADRs), cited by their ids,
such as ADR-2026-10-29-2014. Each citation links to the ADR in the
appendix, which holds every ADR.

# Abstract syntax

The abstract syntax is parameterized over the dialect. A dialect supplies its
op instances and its types; a module of any dialect is made of the same
functions, blocks and ops.

{includeReadable "." Fir.Syntax.Dialect "Dialects" FirSpec.Syntax.Dialect (level := 2)}

{includeReadable "." Fir.Syntax.Location "Locations" FirSpec.Syntax.Location (level := 2)}

{includeReadable "." Fir.Syntax.Module "Modules, functions, blocks and ops" FirSpec.Syntax.Module (level := 2)}

{includeReadable "." Fir.Core.Types "Core types" FirSpec.Core.Types (level := 2)}

{includeReadable "." Fir.Core.Ops "Core ops" FirSpec.Core.Ops (level := 2)}

{includeReadable "." Fir.Core.Signature "Core signatures" FirSpec.Core.Signature (level := 2)}

# Validation

{includeReadable "." Fir.Validation.Scope "Scope and symbols" FirSpec.Validation.Scope (level := 2)}

{includeReadable "." Fir.Validation.Dominance "Dominance" FirSpec.Validation.Dominance (level := 2)}

{includeReadable "." Fir.Validation.Rules "The general rules" FirSpec.Validation.Rules (level := 2)}

{includeReadable "." Fir.Core.Validation "Core rules" FirSpec.Core.Validation (level := 2)}

{includeReadable "." Fir.Core.Rejects "A rejected function" FirSpec.Core.Rejects (level := 2)}

{includeReadable "." Fir.Validation.Check "The validation check" FirSpec.Validation.Check (level := 2)}

{includeReadable "." Fir.Validation.Tables "Tables" FirSpec.Validation.Tables (level := 2)}

{includeReadable "." Fir.Validation.Search "Searching a graph" FirSpec.Validation.Search (level := 2)}

{includeReadable "." Fir.Validation.Graph "Reachability and dominance, decided" FirSpec.Validation.Graph (level := 2)}

{includeReadable "." Fir.Validation.CheckOps "Checking ops" FirSpec.Validation.CheckOps (level := 2)}

{includeReadable "." Fir.Validation.CheckFuncs "Checking functions" FirSpec.Validation.CheckFuncs (level := 2)}

{includeReadable "." Fir.Validation.CheckModule "Checking modules" FirSpec.Validation.CheckModule (level := 2)}

{includeReadable "." Fir.Core.Check "The core dialect's rules, decided" FirSpec.Core.Check (level := 2)}

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

{includeLiterate "." Fir.Execution.Interpreter "The interpreter" (level := 2)}

{includeLiterate "." Fir.Core.Arith "Arithmetic rules" (level := 2)}

{includeLiterate "." Fir.Core.Wrap "Wrap flag rules" (level := 2)}

{includeLiterate "." Fir.Core.Freeze "The freeze rule" (level := 2)}

{includeLiterate "." Fir.Core.Bitwise "Bitwise and shift rules" (level := 2)}

{includeLiterate "." Fir.Core.Width "Width change rules" (level := 2)}

{includeLiterate "." Fir.Core.Div "Division rules" (level := 2)}

{includeLiterate "." Fir.Core.Compare "Comparison and selection rules" (level := 2)}

{includeLiterate "." Fir.Core.Control "Control-flow rules" (level := 2)}

{includeLiterate "." Fir.Core.Branch "Branch rules" (level := 2)}

{includeLiterate "." Fir.Core.Call "Call rules" (level := 2)}

{includeLiterate "." Fir.Core.Semantics "Core op semantics" (level := 2)}

{includeLiterate "." Fir.Core.ArithLaws "Constant obligations" (level := 2)}

{includeLiterate "." Fir.Core.WrapLaws "Arithmetic obligations" (level := 2)}

{includeLiterate "." Fir.Core.FreezeLaws "Freeze obligations" (level := 2)}

{includeLiterate "." Fir.Core.BitwiseLaws "Bitwise and shift obligations" (level := 2)}

{includeLiterate "." Fir.Core.WidthLaws "Width change obligations" (level := 2)}

{includeLiterate "." Fir.Core.DivLaws "Division obligations" (level := 2)}

{includeLiterate "." Fir.Core.CompareLaws "Comparison and selection obligations" (level := 2)}

{includeLiterate "." Fir.Core.ControlLaws "Control-flow obligations" (level := 2)}

{includeLiterate "." Fir.Core.BranchLaws "Branch obligations" (level := 2)}

{includeLiterate "." Fir.Execution.Morphism "Monad morphisms" (level := 2)}

{includeLiterate "." Fir.Execution.ChoiceTree "Choice trees" (level := 2)}

{includeLiterate "." Fir.Execution.Modes "Exhaustive, scripted and sampled modes" (level := 2)}

{includeLiterate "." Fir.Core.Modes "The core dialect's modes" (level := 2)}

{includeLiterate "." Fir.Execution.SetRuns "Reading a run path by path" (level := 2)}

{includeLiterate "." Fir.Execution.Monotone "The runs of a function, and fuel monotonicity" (level := 2)}

{includeLiterate "." Fir.Execution.Environment "The environment of a run" (level := 2)}

{includeLiterate "." Fir.Execution.Progress "Progress and no stuck path" (level := 2)}

{includeLiterate "." Fir.Execution.Scoped "Scope along a run" (level := 2)}

{includeLiterate "." Fir.Execution.Jumps "Progress with jumps and loops" (level := 2)}

{includeReadable "." Fir.Execution.CallSteps "What a call step needs" FirSpec.Execution.CallSteps (level := 2)}

{includeLiterate "." Fir.Execution.Calls "Progress with calls" (level := 2)}

{includeLiterate "." Fir.Core.Runs "The runs of core functions" (level := 2)}

{includeLiterate "." Fir.Core.CallFree "Core functions without calls" (level := 2)}

{includeLiterate "." Fir.Core.ValidRuns "Core functions with calls" (level := 2)}

{includeLiterate "." Fir.Execution.RunPaths "The ways a step goes on" (level := 2)}

{includeLiterate "." Fir.Execution.EnvRefine "Refined environments" (level := 2)}

{includeLiterate "." Fir.Execution.BlackBox "Calls as black boxes" (level := 2)}

{includeLiterate "." Fir.Execution.RefineUp "Returns and UB, followed back" (level := 2)}

{includeLiterate "." Fir.Execution.RefineDown "Running out of fuel, followed back" (level := 2)}

{includeLiterate "." Fir.Execution.RefineRuns "Refined arguments" (level := 2)}

{includeLiterate "." Fir.Execution.Replace "Replacing a callee" (level := 2)}

{includeLiterate "." Fir.Core.CallRefine "Refinement through core calls" (level := 2)}

{includeLiterate "." Fir.Execution.Lawful "What the lawful class gives" (level := 2)}

{includeLiterate "." Fir.Core.Lawful "The core dialect's poison obligations" (level := 2)}

# Text format

{includeLiterate "." Fir.Text.Lexical "Tokens" (level := 2)}

{includeLiterate "." Fir.Text.Grammar "Grammar" (level := 2)}

{includeLiterate "." Fir.Core.Text "The core dialect in text" (level := 2)}

{includeLiterate "." Fir.Text.Print "The canonical printer" (level := 2)}

{includeLiterate "." Fir.Text.RoundTrip "Round trips" (level := 2)}

{includeLiterate "." Fir.Core.TextLaws "The core dialect's text is lawful" (level := 2)}

{includeLiterate "." Fir.Text.Lex "The parser" (level := 2)}

{includeLiterate "." Fir.Text.Read "Reading the grammar" (level := 2)}

{includeLiterate "." Fir.Text.ReadLocs "Reading the location table and the module" (level := 2)}

{includeLiterate "." Fir.Text.Decode "Decoding" (level := 2)}

{includeLiterate "." Fir.Text.Example "Example" (level := 2)}

{includeLiterate "." Fir.Text.Tokens "Lexing printed text" (level := 2)}

{includeLiterate "." Fir.Text.LexNumbers "Digits and their values" (level := 2)}

{includeLiterate "." Fir.Text.LexTokens "Maximal munch" (level := 2)}

{includeLiterate "." Fir.Text.LexStrings "Escapes and quoted symbols" (level := 2)}

{includeLiterate "." Fir.Text.LexLayout "Spaces, line feeds and lists" (level := 2)}

{includeLiterate "." Fir.Text.LexPrint "Attributes, locations and names" (level := 2)}

{includeLiterate "." Fir.Text.LexModule "Ops, functions and the module" (level := 2)}

{includeLiterate "." Fir.Text.LexWellFormed "Writable tokens" (level := 2)}

{includeLiterate "." Fir.Text.Tree "The tree that the grammar reads" (level := 2)}

{includeLiterate "." Fir.Text.ReadAttrs "The grammar step" (level := 2)}

{includeLiterate "." Fir.Text.ReadDefs "Definitions and successors read back" (level := 2)}

{includeLiterate "." Fir.Text.ReadOps "Ops read back" (level := 2)}

{includeLiterate "." Fir.Text.ReadBlocks "Blocks and regions read back" (level := 2)}

{includeLiterate "." Fir.Text.ReadFunc "A function read back" (level := 2)}

{includeLiterate "." Fir.Text.ReadTable "The location table read back" (level := 2)}

{includeLiterate "." Fir.Text.ReadModule "The module read back" (level := 2)}

{includeLiterate "." Fir.Text.DecodeScope "The decoding step" (level := 2)}

{includeLiterate "." Fir.Text.DecodeBlocks "Blocks and ops decoded back" (level := 2)}

{includeLiterate "." Fir.Text.DecodeModule "The module decoded back" (level := 2)}

{includeLiterate "." Fir.Text.PrintParse "The round trip, proved" (level := 2)}

{includeLiterate "." Fir.Text.LexAccepted "What the lexer accepts" (level := 2)}

{includeLiterate "." Fir.Text.ReadAccepted "What the grammar accepts" (level := 2)}

{includeLiterate "." Fir.Text.ReadAcceptedBlocks "Accepted ops, blocks and regions" (level := 2)}

{includeLiterate "." Fir.Text.ReadAcceptedItems "Accepted items" (level := 2)}

{includeLiterate "." Fir.Text.ReadAcceptedModule "An accepted location table" (level := 2)}

{includeLiterate "." Fir.Text.DecodeAcceptedScope "What the first pass accepts" (level := 2)}

{includeLiterate "." Fir.Text.DecodeAccepted "What the second pass accepts" (level := 2)}

{includeLiterate "." Fir.Text.DecodeAcceptedModule "What decoding accepts" (level := 2)}

{includeLiterate "." Fir.Text.ParseWellFormed "Parsed modules are well formed" (level := 2)}

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
