import FirRef.Decode.Scope

/-!
The second pass of the decoder that `fir-ref` runs: `decodeFrames` decodes a
function's blocks in its scope, as the spec's `decodeBlocks`, `decodeOps`
and `decodeRegions` do, with no stack per level of regions and none per
block or op (ADR-2026-10-30-1450).

It builds a tree, so its frames hold what is decoded so far as well as what
is left. A frame of blocks belongs to a region, a frame of ops to a block,
and a frame of regions to an op. Each holds the parts of its owner decoded
so far, last first, and the parts left to decode; the frames of ops and
regions also hold the owner itself, with no ops or regions yet. When a
frame has nothing left, the loop completes its owner and adds it to the
frame below, which goes on with its own parts. The frame of blocks at the
bottom of the stack holds the function's body.

`runTreeFrames` says what a stack of frames means by the spec's functions:
the top frame's parts that are left are decoded by the spec, its owner is
completed, and `finish` hands it to the frames below in turn. Both are
defined on every stack, so the loop and its meaning also agree on a stack
that the loop never builds, such as a frame of ops on a frame of ops.
-/

namespace FirRef

open Fir Fir.Text

variable {d : Dialect}

/-- A step of `Except` that succeeds goes on with its value. -/
theorem ok_bind {ε α β : Type} (a : α) (k : α → Except ε β) : (Except.ok a >>= k) = k a := rfl

/-- What is left of a function's blocks to decode, and what is decoded so
far. -/
inductive TreeFrame (d : Dialect) where
  /-- The blocks of a region: those decoded, last first, and those left. -/
  | blocks (done : List (Block d)) (rest : List SBlock)
  /-- The ops of the block `b`, whose body is empty: those decoded, last
  first, and those left. -/
  | ops (b : Block d) (done : List (Operation d)) (rest : List SOp)
  /-- The regions of the op `o`, which has none: those decoded, last first,
  and those left. -/
  | regions (o : Operation d) (done : List (Region d)) (rest : List SRegion)

/-- A measure of a frame. -/
def TreeFrame.weight : TreeFrame d → Nat
  | .blocks _ bs => sblocksWeight bs + 1
  | .ops _ _ os => sopsWeight os + 1
  | .regions _ _ rs => sregionsWeight rs + 1

/-- A measure of a stack of frames. -/
def treeFramesWeight : List (TreeFrame d) → Nat
  | [] => 0
  | f :: fs => f.weight + treeFramesWeight fs

/-- `Text.operandTypes`, with the types found so far, last first, in `ts`.
Its only call to itself is a tail call. -/
def operandTypes (sc : Scope d) (f : String) (ts : List d.Ty) :
    List (Name × TextPos) → Except ParseError (List d.Ty)
  | [] => pure ts.reverse
  | (x, p) :: xs => match sc[x]? with
    | some t => operandTypes sc f (t :: ts) xs
    | none => errorAt p ("value %" ++ x ++ " is not defined in " ++ printSymbol f)

theorem operandTypes_eq (sc : Scope d) (f : String) (ts : List d.Ty)
    (xs : List (Name × TextPos)) :
    operandTypes sc f ts xs = (do pure (ts.reverse ++ (← Text.operandTypes sc f xs))) := by
  induction xs generalizing ts with
  | nil => simp [operandTypes, Text.operandTypes]
  | cons x xs ih =>
    obtain ⟨x, p⟩ := x
    simp only [operandTypes, Text.operandTypes]
    cases sc[x]? with
    | none => rfl
    | some t => simp [ih]

variable [DialectText d]

/-- Decodes the parts of a function's blocks that each frame leaves, the
top of the stack first, in the scope `sc` of the function `f`. Every call
is a tail call. -/
def decodeFrames (sc : Scope d) (f : String) :
    List (TreeFrame d) → Except ParseError (List (Block d))
  | [] => pure []
  | .blocks done [] :: fs => match fs with
    | [] => pure done.reverse
    | .regions o rs rest :: fs =>
      decodeFrames sc f (.regions o (⟨done.reverse⟩ :: rs) rest :: fs)
    | _ => pure []
  | .blocks done (⟨label, params, ops⟩ :: bs) :: fs => do
    let params ← params.mapM decodeDef
    decodeFrames sc f (.ops ⟨label, params, []⟩ [] ops :: .blocks done bs :: fs)
  | .ops b done [] :: fs => match fs with
    | .blocks bs rest :: fs =>
      decodeFrames sc f (.blocks ({ b with body := done.reverse } :: bs) rest :: fs)
    | _ => pure []
  | .ops b done (⟨results, name, namePos, attrs, operands, succs, regions, loc⟩ :: os) :: fs => do
    let ts ← operandTypes sc f [] operands
    let results ← results.mapM decodeDef
    match decodeOp name attrs ts (results.map (·.2)) with
    | none => errorAt namePos ("op " ++ name ++ " does not decode: the dialect has no op " ++
        "with this name and these attributes, operand types and result types")
    | some op =>
      let o : Operation d := ⟨results, op, operands.map (·.1), succs, [], loc⟩
      decodeFrames sc f (.regions o [] regions :: .ops b done os :: fs)
  | .regions o done [] :: fs => match fs with
    | .ops b os rest :: fs =>
      decodeFrames sc f (.ops b ({ o with regions := done.reverse } :: os) rest :: fs)
    | _ => pure []
  | .regions o done (⟨bs⟩ :: rs) :: fs =>
    decodeFrames sc f (.blocks [] bs :: .regions o done rs :: fs)
termination_by fs => treeFramesWeight fs
decreasing_by
  all_goals
    simp only [treeFramesWeight, TreeFrame.weight, sopsWeight, sopWeight, sblocksWeight,
      sregionsWeight]
    omega

/-- What a frame with nothing left completes: a region, a block or an
op. -/
inductive Decoded (d : Dialect) where
  /-- A region. -/
  | region (r : Region d)
  /-- A block. -/
  | block (b : Block d)
  /-- An op. -/
  | op (o : Operation d)

/-- Hands what a frame completed to the frame on top of `fs`, which decodes
what it has left by the spec's functions, completes its own owner and hands
it on in turn. On an empty stack, the region completed is the function's
body. -/
def finish (sc : Scope d) (f : String) :
    Decoded d → List (TreeFrame d) → Except ParseError (List (Block d))
  | .region r, fs => match fs with
    | [] => pure r.blocks
    | .regions o rs rest :: fs => do
      let more ← Text.decodeRegions sc f rest
      finish sc f (.op { o with regions := (r :: rs).reverse ++ more }) fs
    | _ => pure []
  | .block b, fs => match fs with
    | .blocks bs rest :: fs => do
      let more ← Text.decodeBlocks sc f rest
      finish sc f (.region ⟨(b :: bs).reverse ++ more⟩) fs
    | _ => pure []
  | .op o, fs => match fs with
    | .ops b os rest :: fs => do
      let more ← Text.decodeOps sc f rest
      finish sc f (.block { b with body := (o :: os).reverse ++ more }) fs
    | _ => pure []

/-- What `decodeFrames` computes from a stack, by the spec's functions. -/
def runTreeFrames (sc : Scope d) (f : String) :
    List (TreeFrame d) → Except ParseError (List (Block d))
  | [] => pure []
  | .blocks bs rest :: fs => do
    let more ← Text.decodeBlocks sc f rest
    finish sc f (.region ⟨bs.reverse ++ more⟩) fs
  | .ops b os rest :: fs => do
    let more ← Text.decodeOps sc f rest
    finish sc f (.block { b with body := os.reverse ++ more }) fs
  | .regions o rs rest :: fs => do
    let more ← Text.decodeRegions sc f rest
    finish sc f (.op { o with regions := rs.reverse ++ more }) fs

/-- The loop decodes what the spec's functions decode, and fails where they
fail. -/
theorem decodeFrames_eq (sc : Scope d) (f : String) (fs : List (TreeFrame d)) :
    decodeFrames sc f fs = runTreeFrames sc f fs := by
  fun_induction decodeFrames sc f fs with
  | case1 => rfl
  | case2 => simp [runTreeFrames, finish, Text.decodeBlocks]
  | case3 done o rs rest fs ih =>
    simp only [List.unattach_reverse, List.unattach_attach] at ih
    rw [ih]
    simp [runTreeFrames, finish, Text.decodeBlocks]
  | case4 done fs h1 h2 =>
    simp only [runTreeFrames, finish, Text.decodeBlocks, pure_bind]
  | case5 done label params ops bs fs ih =>
    simp only [ih, runTreeFrames, finish, Text.decodeBlocks, decodeDef_eq]
    simp
  | case6 b done bs rest fs ih =>
    simp only [List.unattach_reverse, List.unattach_attach] at ih
    rw [ih]
    simp [runTreeFrames, finish, Text.decodeOps]
  | case7 b done fs h =>
    simp only [runTreeFrames, finish, Text.decodeOps, pure_bind]
  | case8 b done results name namePos attrs operands succs regions loc os fs ih =>
    simp only [List.attach_map_val] at ih
    simp only [operandTypes_eq, runTreeFrames, Text.decodeOps, decodeDef_eq]
    simp only [List.reverse_nil, List.nil_append, bind_pure_comp]
    cases Text.operandTypes sc f operands with
    | error => rfl
    | ok ts =>
      simp only [ok_bind, pure_bind]
      cases results.mapM (Text.decodeDef (d := d)) with
      | error => rfl
      | ok results =>
        simp only [ok_bind]
        cases decodeOp name attrs ts (results.map (·.2)) with
        | none => rfl
        | some op => simp [ih, runTreeFrames, finish]
  | case9 o done b os rest fs ih =>
    simp only [List.unattach_reverse, List.unattach_attach] at ih
    rw [ih]
    simp [runTreeFrames, finish, Text.decodeRegions]
  | case10 o done fs h =>
    simp only [runTreeFrames, finish, Text.decodeRegions, pure_bind]
  | case11 o done bs rs fs ih =>
    rw [ih]
    simp [runTreeFrames, finish, Text.decodeRegions]

/-- The loop decodes a function's blocks as the spec's `decodeBlocks`
does. -/
theorem decodeFrames_blocks (sc : Scope d) (f : String) (bs : List SBlock) :
    decodeFrames sc f [.blocks [] bs] = Text.decodeBlocks sc f bs := by
  simp [decodeFrames_eq, runTreeFrames, finish]

end FirRef
