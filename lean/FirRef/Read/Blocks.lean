import FirRef.Read.BlocksSpec

/-!
Blocks hold ops, and ops hold regions of blocks, to any depth. `blocksLoop`
reads blocks with an explicit stack of frames, one per construct it is
inside, each with its parts read so far, last first:

* a frame of blocks belongs to a region, or to a function's body at the
  bottom of the stack;
* a frame of ops belongs to a block, whose label and arguments it holds;
* a frame of regions belongs to an op, whose head it holds.

When a frame's next token does not continue it, the loop completes its
owner and adds it to the frame below. Every call to itself is a tail call.
`bRun` says what a stack of frames means by the spec's readers: the top
frame's parts that are left are read by the spec, and `bFinish` hands the
owner it completes to the frames below in turn. Both are defined on every
stack, so the loop and its meaning also agree on stacks that the loop never
builds.
-/

namespace FirRef

open Fir Fir.Text Cursor

/-- What is left to read of a block, an op or a region. -/
inductive BFrame where
  /-- The blocks of a region or a function's body, those read last first. -/
  | blocks (done : List SBlock)
  /-- The ops of the block with this label and these arguments. -/
  | ops (label : Name) (params : List SDef) (done : List SOp)
  /-- The regions of the op with this head. -/
  | regions (head : OpHead) (done : List SRegion)

/-- One more than twice the measure when a frame of ops is on top: the
loop completes a block without reading a token. -/
def BFrame.rank : List BFrame → Nat
  | .ops .. :: _ => 1
  | _ => 0

variable {σ : Type} [Cursor σ]

theorem readOpLocC_lt {s s' : σ} {loc : LocRef} (h : readOpLocC s = .ok (loc, s')) :
    (view s').length < (view s).length := by
  unfold readOpLocC opLocOf at h
  split at h
  · rename_i r p s₁ hs
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ length_lt hs
  · rw [failC_eq] at h
    cases hv : view s <;> rw [hv] at h <;> cases h

/-- Reads the blocks, ops and regions that the frames `fs` leave. -/
def blocksLoop (s : σ) (fs : List BFrame) : Except ParseError (List SBlock × σ) :=
  match fs with
  | [] => .ok ([], s)
  | .blocks done :: fs =>
    match _h : uncons s with
    | some (⟨.label l, _⟩, s₁) =>
      match _hh : blockHeadC s₁ with
      | .ok (params, s₂) => blocksLoop s₂ (.ops l params [] :: .blocks done :: fs)
      | .error e => .error e
    | _ =>
      match fs with
      | [] => .ok (done.reverse, s)
      | .regions hd rs :: fs =>
        match _he : expectC .rbrace "a block or } to close the region" s with
        | .ok ((), s₁) => blocksLoop s₁ (.regions hd (⟨done.reverse⟩ :: rs) :: fs)
        | .error e => .error e
      | _ => .ok ([], s)
  | .ops l params done :: fs =>
    match _h : uncons s with
    | some (⟨.value n, p⟩, s₁) =>
      match _hh : opWithResultsHeadC n p s₁ with
      | .ok (hd, s₂) => blocksLoop s₂ (.regions hd [] :: .ops l params done :: fs)
      | .error e => .error e
    | some (⟨.word w, p⟩, s₁) =>
      match _hh : opBodyHeadC [] w p s₁ with
      | .ok (hd, s₂) => blocksLoop s₂ (.regions hd [] :: .ops l params done :: fs)
      | .error e => .error e
    | _ =>
      match fs with
      | .blocks bs :: fs => blocksLoop s (.blocks (⟨l, params, done.reverse⟩ :: bs) :: fs)
      | _ => .ok ([], s)
  | .regions hd done :: fs =>
    match _h : uncons s with
    | some (⟨.lbrace, _⟩, s₁) => blocksLoop s₁ (.blocks [] :: .regions hd done :: fs)
    | u =>
      match _hl : opLocOf s u with
      | .ok (loc, s₁) =>
        match fs with
        | .ops l params os :: fs => blocksLoop s₁ (.ops l params (hd.op done.reverse loc :: os) :: fs)
        | _ => .ok ([], s₁)
      | .error e => .error e
termination_by 2 * (view s).length + BFrame.rank fs
decreasing_by
  all_goals simp only [BFrame.rank]
  · have := blockHeadC_le _hh
    have := length_lt _h
    omega
  · have := expectC_lt _he
    omega
  · have := opWithResultsHeadC_le _hh
    have := length_lt _h
    omega
  · have := opBodyHeadC_le _hh
    have := length_lt _h
    omega
  · omega
  · have := length_lt _h
    omega
  · have := readOpLocC_lt (s := s) (by rw [readOpLocC, _h]; exact _hl)
    omega

/-- What a frame completes: the blocks of a region or a body, a block, or
an op. -/
inductive BDone where
  | blocks (bs : List SBlock)
  | block (b : SBlock)
  | op (o : SOp)

/-- Hands what a frame completed to the frames `fs`, which read on by the
spec's readers. -/
def bFinish : BDone → List Token → List BFrame → Except ParseError (List SBlock × List Token)
  | .blocks bs, ts, [] => .ok (bs, ts)
  | .blocks bs, ts, .regions hd rs :: fs => do
    let ((), r₁) ← U (expect .rbrace "a block or } to close the region" ts)
    let (more, r₂) ← U (readRegions r₁)
    let (loc, r₃) ← U (readOpLoc r₂)
    bFinish (.op (hd.op ((⟨bs⟩ :: rs).reverse ++ more) loc)) r₃ fs
  | .op o, ts, .ops l ps os :: fs => do
    let (more, r) ← U (readOps ts)
    bFinish (.block ⟨l, ps, (o :: os).reverse ++ more⟩) r fs
  | .block b, ts, .blocks bs :: fs => do
    let (more, r) ← U (readBlocks ts)
    bFinish (.blocks ((b :: bs).reverse ++ more)) r fs
  | _, ts, _ => .ok ([], ts)

/-- What `blocksLoop` computes from the frames `fs`, by the spec's
readers. -/
def bRun (ts : List Token) : List BFrame → Except ParseError (List SBlock × List Token)
  | [] => .ok ([], ts)
  | .blocks done :: fs => do
    let (bs, r) ← U (readBlocks ts)
    bFinish (.blocks (done.reverse ++ bs)) r fs
  | .ops l ps done :: fs => do
    let (os, r) ← U (readOps ts)
    bFinish (.block ⟨l, ps, done.reverse ++ os⟩) r fs
  | .regions hd done :: fs => do
    let (rs, r) ← U (readRegions ts)
    let (loc, r') ← U (readOpLoc r)
    bFinish (.op (hd.op (done.reverse ++ rs) loc)) r' fs

end FirRef
