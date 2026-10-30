import Fir.Text.Decode
import FirRef.PrintAttr

/-!
`fir-ref` decodes with `FirRef.decodeModule`, not with the spec's
`Text.decodeModule` (ADR-2026-10-30-1450). The spec decodes a function in
two passes. Both recurse once per level of regions without a tail call, and
the second also once per block of a region and per op of a block. This
module holds the first pass, which builds the function's scope, and copies
of the spec's functions that it calls; `FirRef.Decode.Tree` holds the
second.

`decodeType`, `decodeDef` and `define` are the spec's definitions, compiled
after `print_eq_printAttr`: the message on a type that does not decode
prints the type with `printAttr`, in linear time and with no stack per
level. Each is equal to its spec function by `rfl` or by induction.

`defineFrames` adds the definitions of blocks, ops and regions to a scope
in the order of the spec's `defineBlocks`, `defineOps` and `defineRegions`,
so it stops at the same first error. It keeps what is left on an explicit
stack of frames, and each of its calls is a tail call.
-/

namespace FirRef

open Fir Fir.Text

mutual
/-- A measure of an op as written that each step of the decoder's loops
lowers. -/
def sopWeight : SOp → Nat
  | ⟨_, _, _, _, _, _, rs, _⟩ => sregionsWeight rs + 1

/-- A measure of ops as written. -/
def sopsWeight : List SOp → Nat
  | [] => 0
  | o :: os => sopWeight o + sopsWeight os + 3

/-- A measure of blocks as written. -/
def sblocksWeight : List SBlock → Nat
  | [] => 0
  | ⟨_, _, os⟩ :: bs => sopsWeight os + sblocksWeight bs + 3

/-- A measure of regions as written. -/
def sregionsWeight : List SRegion → Nat
  | [] => 0
  | ⟨bs⟩ :: rs => sblocksWeight bs + sregionsWeight rs + 3
end

/-- What is left of a function's blocks to add to its scope. -/
inductive ScopeFrame where
  /-- Blocks. -/
  | blocks (bs : List SBlock)
  /-- Ops. -/
  | ops (os : List SOp)
  /-- The regions of an op. -/
  | regions (rs : List SRegion)

/-- A measure of a frame. -/
def ScopeFrame.weight : ScopeFrame → Nat
  | .blocks bs => sblocksWeight bs + 1
  | .ops os => sopsWeight os + 1
  | .regions rs => sregionsWeight rs + 1

/-- A measure of a stack of frames. -/
def scopeFramesWeight : List ScopeFrame → Nat
  | [] => 0
  | f :: fs => f.weight + scopeFramesWeight fs

variable {d : Dialect} [DialectText d]

/-- `Text.decodeType`, compiled after `print_eq_printAttr`. -/
def decodeType (a : Attr) (p : TextPos) : Except ParseError d.Ty :=
  match decodeTy a with
  | some t => .ok t
  | none => errorAt p ("type " ++ a.print ++ " does not decode")

theorem decodeType_eq : @decodeType = @Text.decodeType := rfl

/-- `Text.decodeDef`, with `decodeType`. -/
def decodeDef (x : SDef) : Except ParseError (Name × d.Ty) := do
  pure (x.name, ← decodeType x.ty x.tyPos)

theorem decodeDef_eq : @decodeDef = @Text.decodeDef := rfl

/-- `Text.define`, with `decodeDef`. Its only call to itself is a tail
call. -/
def define (sc : Scope d) : List SDef → Except ParseError (Scope d)
  | [] => pure sc
  | x :: xs => do
    let (n, t) ← decodeDef x
    if sc.contains n then errorAt x.pos ("value %" ++ n ++ " is defined twice")
    else define (sc.insert n t) xs

theorem define_eq : @define = @Text.define := by
  funext d _ sc xs
  induction xs generalizing sc with
  | nil => rfl
  | cons x xs ih => simp only [define, Text.define, decodeDef_eq, ih]

/-- What a frame adds to the scope, by the spec's functions. -/
def ScopeFrame.run (sc : Scope d) : ScopeFrame → Except ParseError (Scope d)
  | .blocks bs => Text.defineBlocks sc bs
  | .ops os => Text.defineOps sc os
  | .regions rs => Text.defineRegions sc rs

/-- Adds what each frame defines to the scope, the top of the stack first,
by the spec's functions. -/
def runScopeFrames (sc : Scope d) : List ScopeFrame → Except ParseError (Scope d)
  | [] => pure sc
  | f :: fs => do runScopeFrames (← f.run sc) fs

/-- Adds what each frame defines to the scope, the top of the stack first:
`runScopeFrames`, with no stack per level. Every call is a tail call. -/
def defineFrames (sc : Scope d) : List ScopeFrame → Except ParseError (Scope d)
  | [] => pure sc
  | .blocks [] :: fs => defineFrames sc fs
  | .blocks (⟨_, params, ops⟩ :: bs) :: fs => do
    defineFrames (← define sc params) (.ops ops :: .blocks bs :: fs)
  | .ops [] :: fs => defineFrames sc fs
  | .ops (⟨results, _, _, _, _, _, regions, _⟩ :: os) :: fs => do
    defineFrames (← define sc results) (.regions regions :: .ops os :: fs)
  | .regions [] :: fs => defineFrames sc fs
  | .regions (⟨bs⟩ :: rs) :: fs => defineFrames sc (.blocks bs :: .regions rs :: fs)
termination_by fs => scopeFramesWeight fs
decreasing_by
  all_goals
    simp only [scopeFramesWeight, ScopeFrame.weight, sopsWeight, sopWeight, sblocksWeight,
      sregionsWeight]
    omega

/-- The loop adds what the spec's functions add, and fails where they
fail. -/
theorem defineFrames_eq (sc : Scope d) (fs : List ScopeFrame) :
    defineFrames sc fs = runScopeFrames sc fs := by
  fun_induction defineFrames sc fs with
  | case1 sc => rfl
  | _ => simp_all [runScopeFrames, ScopeFrame.run, define_eq, Text.defineBlocks, Text.defineOps,
      Text.defineRegions]

/-- The scope of a function's blocks, as the spec's `defineBlocks` builds
it. -/
theorem defineFrames_blocks (sc : Scope d) (bs : List SBlock) :
    defineFrames sc [.blocks bs] = Text.defineBlocks sc bs := by
  simp [defineFrames_eq, runScopeFrames, ScopeFrame.run]

end FirRef
