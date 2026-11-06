import VersoManual
import Fir
import FirSpecSite.ReadableElab
import FirSpec.Syntax.Dialect
import FirSpec.Syntax.Location
import FirSpec.Syntax.Module
import FirSpec.Core.Types
import FirSpec.Core.Ops
import FirSpec.Core.Signature
import FirSpec.Core.Poison
import FirSpec.Core.Unlawful
import FirSpec.Core.Values
import FirSpec.Execution.Behaviour
import FirSpec.Execution.CallSteps
import FirSpec.Execution.Effects
import FirSpec.Execution.Fuel
import FirSpec.Execution.Propagation
import FirSpec.Execution.Refinement
import FirSpec.Execution.Values
import FirSpec.Execution.SetRuns
import FirSpec.Execution.Monotone
import FirSpec.Execution.Environment
import FirSpec.Execution.Progress
import FirSpec.Execution.Scoped
import FirSpec.Execution.Jumps
import FirSpec.Execution.Calls
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
import FirSpec.Core.Runs
import FirSpec.Core.CallFree
import FirSpec.Core.ValidRuns
import FirSpec.Execution.Interpreter
import FirSpec.Core.Arith
import FirSpec.Core.Wrap
import FirSpec.Core.Freeze
import FirSpec.Core.Bitwise
import FirSpec.Core.Width
import FirSpec.Core.Div
import FirSpec.Core.Compare
import FirSpec.Core.Control
import FirSpec.Core.Branch
import FirSpec.Core.Call
import FirSpec.Core.Semantics
import FirSpec.Core.ArithLaws
import FirSpec.Core.WrapLaws
import FirSpec.Core.FreezeLaws
import FirSpec.Core.BitwiseLaws
import FirSpec.Core.WidthLaws
import FirSpec.Core.DivLaws
import FirSpec.Core.CompareLaws
import FirSpec.Core.ControlLaws
import FirSpec.Core.BranchLaws
import FirSpec.Execution.Morphism
import FirSpec.Execution.ChoiceTree
import FirSpec.Execution.Modes
import FirSpec.Core.Modes
import FirSpec.Execution.RunPaths
import FirSpec.Execution.EnvRefine
import FirSpec.Execution.BlackBox
import FirSpec.Execution.RefineUp
import FirSpec.Execution.RefineDown
import FirSpec.Execution.RefineRuns
import FirSpec.Execution.Replace
import FirSpec.Core.CallRefine
import FirSpec.Execution.Lawful
import FirSpec.Core.Lawful
import FirSpec.Text.Lexical
import FirSpec.Text.Grammar
import FirSpec.Core.Text
import FirSpec.Text.Print
import FirSpec.Text.RoundTrip
import FirSpec.Core.TextLaws
import FirSpec.Text.Lex
import FirSpec.Text.Read
import FirSpec.Text.ReadLocs
import FirSpec.Text.Decode
import FirSpec.Text.Example
import FirSpec.Text.Tokens
import FirSpec.Text.LexNumbers
import FirSpec.Text.LexTokens
import FirSpec.Text.LexStrings
import FirSpec.Text.LexLayout
import FirSpec.Text.LexPrint
import FirSpec.Text.LexModule
import FirSpec.Text.LexWellFormed

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

{includeReadable "." Fir.Execution.Values "Values and refinement" FirSpec.Execution.Values (level := 2)}

{includeLiterate "." Fir.Execution.PoisonUB "Poison and immediate UB" (level := 2)}

{includeReadable "." Fir.Execution.Effects "Effects and op semantics" FirSpec.Execution.Effects (level := 2)}

{includeReadable "." Fir.Execution.Behaviour "Outcomes and behaviours" FirSpec.Execution.Behaviour (level := 2)}

{includeReadable "." Fir.Execution.Fuel "Fuel and progress" FirSpec.Execution.Fuel (level := 2)}

{includeReadable "." Fir.Execution.Refinement "Refinement" FirSpec.Execution.Refinement (level := 2)}

{includeReadable "." Fir.Execution.Propagation "Poison classes" FirSpec.Execution.Propagation (level := 2)}

{includeReadable "." Fir.Core.Values "Core values" FirSpec.Core.Values (level := 2)}

{includeReadable "." Fir.Core.Poison "Core poison classes" FirSpec.Core.Poison (level := 2)}

{includeReadable "." Fir.Core.Unlawful "Semantics the obligations reject" FirSpec.Core.Unlawful (level := 2)}

{includeReadable "." Fir.Execution.Interpreter "The interpreter" FirSpec.Execution.Interpreter (level := 2)}

{includeReadable "." Fir.Core.Arith "Arithmetic rules" FirSpec.Core.Arith (level := 2)}

{includeReadable "." Fir.Core.Wrap "Wrap flag rules" FirSpec.Core.Wrap (level := 2)}

{includeReadable "." Fir.Core.Freeze "The freeze rule" FirSpec.Core.Freeze (level := 2)}

{includeReadable "." Fir.Core.Bitwise "Bitwise and shift rules" FirSpec.Core.Bitwise (level := 2)}

{includeReadable "." Fir.Core.Width "Width change rules" FirSpec.Core.Width (level := 2)}

{includeReadable "." Fir.Core.Div "Division rules" FirSpec.Core.Div (level := 2)}

{includeReadable "." Fir.Core.Compare "Comparison and selection rules" FirSpec.Core.Compare (level := 2)}

{includeReadable "." Fir.Core.Control "Control-flow rules" FirSpec.Core.Control (level := 2)}

{includeReadable "." Fir.Core.Branch "Branch rules" FirSpec.Core.Branch (level := 2)}

{includeReadable "." Fir.Core.Call "Call rules" FirSpec.Core.Call (level := 2)}

{includeReadable "." Fir.Core.Semantics "Core op semantics" FirSpec.Core.Semantics (level := 2)}

{includeReadable "." Fir.Core.ArithLaws "Constant obligations" FirSpec.Core.ArithLaws (level := 2)}

{includeReadable "." Fir.Core.WrapLaws "Arithmetic obligations" FirSpec.Core.WrapLaws (level := 2)}

{includeReadable "." Fir.Core.FreezeLaws "Freeze obligations" FirSpec.Core.FreezeLaws (level := 2)}

{includeReadable "." Fir.Core.BitwiseLaws "Bitwise and shift obligations" FirSpec.Core.BitwiseLaws (level := 2)}

{includeReadable "." Fir.Core.WidthLaws "Width change obligations" FirSpec.Core.WidthLaws (level := 2)}

{includeReadable "." Fir.Core.DivLaws "Division obligations" FirSpec.Core.DivLaws (level := 2)}

{includeReadable "." Fir.Core.CompareLaws "Comparison and selection obligations" FirSpec.Core.CompareLaws (level := 2)}

{includeReadable "." Fir.Core.ControlLaws "Control-flow obligations" FirSpec.Core.ControlLaws (level := 2)}

{includeReadable "." Fir.Core.BranchLaws "Branch obligations" FirSpec.Core.BranchLaws (level := 2)}

{includeReadable "." Fir.Execution.Morphism "Monad morphisms" FirSpec.Execution.Morphism (level := 2)}

{includeReadable "." Fir.Execution.ChoiceTree "Choice trees" FirSpec.Execution.ChoiceTree (level := 2)}

{includeReadable "." Fir.Execution.Modes "Exhaustive, scripted and sampled modes" FirSpec.Execution.Modes (level := 2)}

{includeReadable "." Fir.Core.Modes "The core dialect's modes" FirSpec.Core.Modes (level := 2)}

{includeReadable "." Fir.Execution.SetRuns "Reading a run path by path" FirSpec.Execution.SetRuns (level := 2)}

{includeReadable "." Fir.Execution.Monotone "The runs of a function, and fuel monotonicity" FirSpec.Execution.Monotone (level := 2)}

{includeReadable "." Fir.Execution.Environment "The environment of a run" FirSpec.Execution.Environment (level := 2)}

{includeReadable "." Fir.Execution.Progress "Progress and no stuck path" FirSpec.Execution.Progress (level := 2)}

{includeReadable "." Fir.Execution.Scoped "Scope along a run" FirSpec.Execution.Scoped (level := 2)}

{includeReadable "." Fir.Execution.Jumps "Progress with jumps and loops" FirSpec.Execution.Jumps (level := 2)}

{includeReadable "." Fir.Execution.CallSteps "What a call step needs" FirSpec.Execution.CallSteps (level := 2)}

{includeReadable "." Fir.Execution.Calls "Progress with calls" FirSpec.Execution.Calls (level := 2)}

{includeReadable "." Fir.Core.Runs "The runs of core functions" FirSpec.Core.Runs (level := 2)}

{includeReadable "." Fir.Core.CallFree "Core functions without calls" FirSpec.Core.CallFree (level := 2)}

{includeReadable "." Fir.Core.ValidRuns "Core functions with calls" FirSpec.Core.ValidRuns (level := 2)}

{includeReadable "." Fir.Execution.RunPaths "The ways a step goes on" FirSpec.Execution.RunPaths (level := 2)}

{includeReadable "." Fir.Execution.EnvRefine "Refined environments" FirSpec.Execution.EnvRefine (level := 2)}

{includeReadable "." Fir.Execution.BlackBox "Calls as black boxes" FirSpec.Execution.BlackBox (level := 2)}

{includeReadable "." Fir.Execution.RefineUp "Returns and UB, followed back" FirSpec.Execution.RefineUp (level := 2)}

{includeReadable "." Fir.Execution.RefineDown "Running out of fuel, followed back" FirSpec.Execution.RefineDown (level := 2)}

{includeReadable "." Fir.Execution.RefineRuns "Refined arguments" FirSpec.Execution.RefineRuns (level := 2)}

{includeReadable "." Fir.Execution.Replace "Replacing a callee" FirSpec.Execution.Replace (level := 2)}

{includeReadable "." Fir.Core.CallRefine "Refinement through core calls" FirSpec.Core.CallRefine (level := 2)}

{includeReadable "." Fir.Execution.Lawful "What the lawful class gives" FirSpec.Execution.Lawful (level := 2)}

{includeReadable "." Fir.Core.Lawful "The core dialect's poison obligations" FirSpec.Core.Lawful (level := 2)}

# Text format

{includeReadable "." Fir.Text.Lexical "Tokens" FirSpec.Text.Lexical (level := 2)}

{includeReadable "." Fir.Text.Grammar "Grammar" FirSpec.Text.Grammar (level := 2)}

{includeReadable "." Fir.Core.Text "The core dialect in text" FirSpec.Core.Text (level := 2)}

{includeReadable "." Fir.Text.Print "The canonical printer" FirSpec.Text.Print (level := 2)}

{includeReadable "." Fir.Text.RoundTrip "Round trips" FirSpec.Text.RoundTrip (level := 2)}

{includeReadable "." Fir.Core.TextLaws "The core dialect's text is lawful" FirSpec.Core.TextLaws (level := 2)}

{includeReadable "." Fir.Text.Lex "The parser" FirSpec.Text.Lex (level := 2)}

{includeReadable "." Fir.Text.Read "Reading the grammar" FirSpec.Text.Read (level := 2)}

{includeReadable "." Fir.Text.ReadLocs "Reading the location table and the module" FirSpec.Text.ReadLocs (level := 2)}

{includeReadable "." Fir.Text.Decode "Decoding" FirSpec.Text.Decode (level := 2)}

{includeReadable "." Fir.Text.Example "Example" FirSpec.Text.Example (level := 2)}

{includeReadable "." Fir.Text.Tokens "Lexing printed text" FirSpec.Text.Tokens (level := 2)}

{includeReadable "." Fir.Text.LexNumbers "Digits and their values" FirSpec.Text.LexNumbers (level := 2)}

{includeReadable "." Fir.Text.LexTokens "Maximal munch" FirSpec.Text.LexTokens (level := 2)}

{includeReadable "." Fir.Text.LexStrings "Escapes and quoted symbols" FirSpec.Text.LexStrings (level := 2)}

{includeReadable "." Fir.Text.LexLayout "Spaces, line feeds and lists" FirSpec.Text.LexLayout (level := 2)}

{includeReadable "." Fir.Text.LexPrint "Attributes, locations and names" FirSpec.Text.LexPrint (level := 2)}

{includeReadable "." Fir.Text.LexModule "Ops, functions and the module" FirSpec.Text.LexModule (level := 2)}

{includeReadable "." Fir.Text.LexWellFormed "Writable tokens" FirSpec.Text.LexWellFormed (level := 2)}

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
