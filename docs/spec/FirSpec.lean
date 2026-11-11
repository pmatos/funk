import VersoManual
import Fir
import FirSpecSite.ReadableElab
import FirSpec.ReadableDocs
import FirSpec.Chapters.Execution

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
* _Memory_ gives fir's model of memory: allocations as logical blocks of
  abstract units, pointers with provenance, and the accesses that load,
  store, allocate and free, with the laws they obey. It then gives the
  memories of a run, with a frame for each call, the memory effect, the
  state layer that adds memory to a way of computing, the runs with
  memory of a function, and what an op that declares no effect on a memory
  must leave of it.
* _Text format_ gives fir's one canonical text: its tokens, its grammar,
  the printer that fixes its layout, the round-trip properties, and the
  parser, with the proofs that parsing a printed well-formed module gives
  it back and that every module the parser gives is well formed.
* _Sums of dialects_ gives how the ops and types of several dialects
  combine in one module, routed by the prefix of each word, how an
  extension joins a sum that holds what it depends on, and proves that the
  round trip and the poison obligations hold for the sum.

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

{include 1 FirSpec.Chapters.Execution}

# Memory

Memory is logical blocks in typed memories (ADR-2026-11-09-1542). This
chapter gives one memory of that model, written once for a unit of any
width, so that every memory of every dialect is an instance of it. It then
makes memory an effect of a run: the memories of a run, the effect that
ops ask for, the layer that adds the memories to a way of computing, the
runs of a function with memory and how they end, their fuel monotonicity,
the obligations that an op's declaration of its effects on memory puts on
its semantics, progress with memory, which asks each op to be total from
any memories, and refinement with memory, which refines memories unit by
unit and asks each op to be monotone from memories that refine others.

{includeReadable "." Fir.Memory.Model "The memory model" FirSpec.Memory.Model (level := 2)}

{includeReadable "." Fir.Memory.Laws "Memory laws" FirSpec.Memory.Laws (level := 2)}

{includeReadable "." Fir.Memory.Frames "The memories of a run" FirSpec.Memory.Frames (level := 2)}

{includeReadable "." Fir.Memory.FrameLaws "Frame laws" FirSpec.Memory.FrameLaws (level := 2)}

{includeReadable "." Fir.Memory.Refine "Refining memories" FirSpec.Memory.Refine (level := 2)}

{includeReadable "." Fir.Execution.MemoryEffect "The memory effect" FirSpec.Execution.MemoryEffect (level := 2)}

{includeReadable "." Fir.Execution.MemoryState "The state layer" FirSpec.Execution.MemoryState (level := 2)}

{includeReadable "." Fir.Execution.MemoryRuns "Runs with memory" FirSpec.Execution.MemoryRuns (level := 2)}

{includeReadable "." Fir.Execution.StatePaths "How a run with memory ends" FirSpec.Execution.StatePaths (level := 2)}

{includeReadable "." Fir.Execution.MemoryMonotone "Runs with memory at every budget" FirSpec.Execution.MemoryMonotone (level := 2)}

{includeReadable "." Fir.Execution.MemoryObligations "Memory obligations" FirSpec.Execution.MemoryObligations (level := 2)}

{includeReadable "." Fir.Execution.MemoryObligationLaws "Meeting the memory obligations" FirSpec.Execution.MemoryObligationLaws (level := 2)}

{includeReadable "." Fir.Execution.MemoryTotal "Totality with memory" FirSpec.Execution.MemoryTotal (level := 2)}

{includeReadable "." Fir.Execution.MemoryCallSteps "The steps of a call, with memory" FirSpec.Execution.MemoryCallSteps (level := 2)}

{includeReadable "." Fir.Execution.MemoryProgress "Progress and no stuck path, with memory" FirSpec.Execution.MemoryProgress (level := 2)}

{includeReadable "." Fir.Execution.MemoryOpRefine "Monotonicity with memory" FirSpec.Execution.MemoryOpRefine (level := 2)}

{includeReadable "." Fir.Execution.MemoryStepPaths "The ways a step with memory goes on" FirSpec.Execution.MemoryStepPaths (level := 2)}

{includeReadable "." Fir.Execution.MemoryCalls "Runs from given memories" FirSpec.Execution.MemoryCalls (level := 2)}

{includeReadable "." Fir.Execution.MemoryBlackBox "Calls as black boxes, with memory" FirSpec.Execution.MemoryBlackBox (level := 2)}

{includeReadable "." Fir.Execution.MemoryRefineUp "Returns and UB with memory, followed back" FirSpec.Execution.MemoryRefineUp (level := 2)}

{includeReadable "." Fir.Execution.MemoryRefineDown "Running out of fuel with memory, followed back" FirSpec.Execution.MemoryRefineDown (level := 2)}

{includeReadable "." Fir.Execution.MemoryRefineRuns "Refined arguments and memories" FirSpec.Execution.MemoryRefineRuns (level := 2)}

{includeReadable "." Fir.Execution.MemoryReplace "Replacing a callee, with memory" FirSpec.Execution.MemoryReplace (level := 2)}

{includeReadable "." Fir.Core.MemoryRuns "Core functions with memory" FirSpec.Core.MemoryRuns (level := 2)}

# Text format

{includeReadable "." Fir.Text.Lexical "Tokens" FirSpec.Text.Lexical (level := 2)}

{includeReadable "." Fir.Text.Grammar "Grammar" FirSpec.Text.Grammar (level := 2)}

{includeReadable "." Fir.Core.Text "The core dialect in text" FirSpec.Core.Text (level := 2)}

{includeReadable "." Fir.Text.Print "The canonical printer" FirSpec.Text.Print (level := 2)}

{includeReadable "." Fir.Text.RoundTrip "Round trips" FirSpec.Text.RoundTrip (level := 2)}

{includeReadable "." Fir.Core.TypeTextLaws "The core types in text are lawful" FirSpec.Core.TypeTextLaws (level := 2)}

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

{includeReadable "." Fir.Text.Tree "The tree that the grammar reads" FirSpec.Text.Tree (level := 2)}

{includeReadable "." Fir.Text.ReadAttrs "The grammar step" FirSpec.Text.ReadAttrs (level := 2)}

{includeReadable "." Fir.Text.ReadDefs "Definitions and successors read back" FirSpec.Text.ReadDefs (level := 2)}

{includeReadable "." Fir.Text.ReadOps "Ops read back" FirSpec.Text.ReadOps (level := 2)}

{includeReadable "." Fir.Text.ReadBlocks "Blocks and regions read back" FirSpec.Text.ReadBlocks (level := 2)}

{includeReadable "." Fir.Text.ReadFunc "A function read back" FirSpec.Text.ReadFunc (level := 2)}

{includeReadable "." Fir.Text.ReadTable "The location table read back" FirSpec.Text.ReadTable (level := 2)}

{includeReadable "." Fir.Text.ReadModule "The module read back" FirSpec.Text.ReadModule (level := 2)}

{includeReadable "." Fir.Text.DecodeScope "The decoding step" FirSpec.Text.DecodeScope (level := 2)}

{includeReadable "." Fir.Text.DecodeBlocks "Blocks and ops decoded back" FirSpec.Text.DecodeBlocks (level := 2)}

{includeReadable "." Fir.Text.DecodeModule "The module decoded back" FirSpec.Text.DecodeModule (level := 2)}

{includeReadable "." Fir.Text.PrintParse "The round trip, proved" FirSpec.Text.PrintParse (level := 2)}

{includeReadable "." Fir.Text.LexAccepted "What the lexer accepts" FirSpec.Text.LexAccepted (level := 2)}

{includeReadable "." Fir.Text.ReadAccepted "What the grammar accepts" FirSpec.Text.ReadAccepted (level := 2)}

{includeReadable "." Fir.Text.ReadAcceptedBlocks "Accepted ops, blocks and regions" FirSpec.Text.ReadAcceptedBlocks (level := 2)}

{includeReadable "." Fir.Text.ReadAcceptedItems "Accepted items" FirSpec.Text.ReadAcceptedItems (level := 2)}

{includeReadable "." Fir.Text.ReadAcceptedModule "An accepted location table" FirSpec.Text.ReadAcceptedModule (level := 2)}

{includeReadable "." Fir.Text.DecodeAcceptedScope "What the first pass accepts" FirSpec.Text.DecodeAcceptedScope (level := 2)}

{includeReadable "." Fir.Text.DecodeAccepted "What the second pass accepts" FirSpec.Text.DecodeAccepted (level := 2)}

{includeReadable "." Fir.Text.DecodeAcceptedModule "What decoding accepts" FirSpec.Text.DecodeAcceptedModule (level := 2)}

{includeReadable "." Fir.Text.ParseWellFormed "Parsed modules are well formed" FirSpec.Text.ParseWellFormed (level := 2)}

# Sums of dialects

A module that holds the ops of several dialects is a module of their sum,
built one dialect at a time on the core (ADR-2026-11-09-1543,
ADR-2026-11-09-2306). Every word says which dialect it belongs to, by its
prefix, and the sum reads each word with that dialect. An extension is
written over the dialects it depends on, and joins a sum that holds them,
and more, by a lift through an inclusion of types (ADR-2026-11-10-1310), so
extensions written apart combine in one sum.

{includeReadable "." Fir.Sum.Names "Words and dialect sets" FirSpec.Sum.Names (level := 2)}

{includeReadable "." Fir.Core.Names "The core's words are bare" FirSpec.Core.Names (level := 2)}

{includeReadable "." Fir.Validation.DialectSet "A module's dialect set" FirSpec.Validation.DialectSet (level := 2)}

{includeReadable "." Fir.Sum.Dialect "The sum of dialects" FirSpec.Sum.Dialect (level := 2)}

{includeReadable "." Fir.Sum.TextLaws "The text of a sum" FirSpec.Sum.TextLaws (level := 2)}

{includeReadable "." Fir.Sum.PoisonLaws "A sum's poison obligations" FirSpec.Sum.PoisonLaws (level := 2)}

{includeReadable "." Fir.Sum.EffectLaws "A sum's effect obligations" FirSpec.Sum.EffectLaws (level := 2)}

{includeReadable "." Fir.Sum.Inclusion "Inclusions of types" FirSpec.Sum.Inclusion (level := 2)}

{includeReadable "." Fir.Sum.Lift "Lifting an extension" FirSpec.Sum.Lift (level := 2)}

{includeReadable "." Fir.Sum.LiftTextLaws "The text of a lift" FirSpec.Sum.LiftTextLaws (level := 2)}

{includeReadable "." Fir.Sum.LiftPoisonLaws "A lift's poison obligations" FirSpec.Sum.LiftPoisonLaws (level := 2)}

{includeReadable "." Fir.Sum.LiftEffectLaws "A lift's effect obligations" FirSpec.Sum.LiftEffectLaws (level := 2)}

{includeReadable "." Fir.Sum.TotalLaws "Totality of a sum and a lift" FirSpec.Sum.TotalLaws (level := 2)}

{includeReadable "." Fir.Sum.MonotoneLaws "Monotonicity of a sum and a lift" FirSpec.Sum.MonotoneLaws (level := 2)}

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
