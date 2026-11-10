import FirRef.Read.BlocksSpec

/-!
Blocks hold ops, and ops hold regions of blocks, to any depth. `blocksLoop`
reads blocks with an explicit stack of frames, one per construct it is
inside, each with its parts read so far, last first:

* a frame of blocks belongs to a region, whose kind it holds, or to a
  function's body at the bottom of the stack;
* a frame of ops belongs to a block, whose label and arguments it holds;
  it looks at the next token with `startsOpC` before it reads an op with
  `opHeadC`, so that at a block's end it leaves the token, and the frame
  below takes it, without lexing past it;
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
  /-- The blocks of a region of this kind or of a function's body, those
  read last first. -/
  | blocks (kind : Option Name) (done : List SBlock)
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

/-- Whether the next token starts an op: a value, its first result, or a
word, its name. It looks at the token and does not take it. -/
def startsOpC (s : σ) : Bool :=
  match uncons s with
  | some (⟨.value _, _⟩, _) => true
  | some (⟨.word _, _⟩, _) => true
  | _ => false

/-- The head of the op that starts at `s`, with a value or a word. -/
def opHeadC (s : σ) : Except ParseError (OpHead × σ) :=
  match uncons s with
  | some (⟨.value n, p⟩, s₁) => opWithResultsHeadC n p s₁
  | some (⟨.word w, p⟩, s₁) => opBodyHeadC [] w p s₁
  | _ => failC s "an op"

theorem opHeadC_lt {s s' : σ} {hd : OpHead} (h : opHeadC s = .ok (hd, s')) :
    (view s').length < (view s).length := by
  unfold opHeadC at h
  split at h
  · rename_i n p s₁ hs
    have := opWithResultsHeadC_le h
    have := length_lt hs
    omega
  · rename_i w p s₁ hs
    have := opBodyHeadC_le h
    have := length_lt hs
    omega
  · rw [failC_eq] at h
    cases hv : view s <;> rw [hv] at h <;> cases h

theorem opHeadC_cases {s : σ} (hs : startsOpC s = true) :
    (∃ n p s₁, uncons s = some (⟨.value n, p⟩, s₁) ∧ opHeadC s = opWithResultsHeadC n p s₁) ∨
      (∃ w p s₁, uncons s = some (⟨.word w, p⟩, s₁) ∧ opHeadC s = opBodyHeadC [] w p s₁) := by
  unfold startsOpC at hs
  split at hs
  · rename_i n p s₁ h
    exact .inl ⟨n, p, s₁, h, by unfold opHeadC; rw [h]⟩
  · rename_i w p s₁ h
    exact .inr ⟨w, p, s₁, h, by unfold opHeadC; rw [h]⟩
  · cases hs

theorem startsOpC_false {s : σ} (hs : ¬startsOpC s = true) :
    (∀ n p s₁, uncons s = some (⟨.value n, p⟩, s₁) → False) ∧
      (∀ w p s₁, uncons s = some (⟨.word w, p⟩, s₁) → False) := by
  constructor
  · intro n p s₁ h
    exact hs (by unfold startsOpC; rw [h])
  · intro w p s₁ h
    exact hs (by unfold startsOpC; rw [h])

/-- Reads the blocks, ops and regions that the frames `fs` leave. -/
def blocksLoop (s : σ) (fs : List BFrame) : Except ParseError (List SBlock × σ) :=
  match fs with
  | [] => .ok ([], s)
  | .blocks kind done :: fs =>
    match _h : uncons s with
    | some (⟨.label l, _⟩, s₁) =>
      match _hh : blockHeadC s₁ with
      | .ok (params, s₂) => blocksLoop s₂ (.ops l params [] :: .blocks kind done :: fs)
      | .error e => .error e
    | _ =>
      match fs with
      | [] => .ok (done.reverse, s)
      | .regions hd rs :: fs =>
        match _he : expectC .rbrace "a block or } to close the region" s with
        | .ok ((), s₁) => blocksLoop s₁ (.regions hd (⟨kind, done.reverse⟩ :: rs) :: fs)
        | .error e => .error e
      | _ => .ok ([], s)
  | .ops l params done :: fs =>
    if _hs : startsOpC s then
      match _hh : opHeadC s with
      | .ok (hd, s₂) => blocksLoop s₂ (.regions hd [] :: .ops l params done :: fs)
      | .error e => .error e
    else
      match fs with
      | .blocks k bs :: fs => blocksLoop s (.blocks k (⟨l, params, done.reverse⟩ :: bs) :: fs)
      | _ => .ok ([], s)
  | .regions hd done :: fs =>
    match _h : uncons s with
    | some (⟨.lbrace, _⟩, s₁) =>
      match _hk : uncons s₁ with
      | some (⟨.word k, _⟩, s₂) => blocksLoop s₂ (.blocks (some k) [] :: .regions hd done :: fs)
      | _ => blocksLoop s₁ (.blocks none [] :: .regions hd done :: fs)
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
  · have := opHeadC_lt _hh
    omega
  · omega
  · have := length_lt _h
    have := length_lt _hk
    omega
  · have := length_lt _h
    omega
  · have := readOpLocC_lt (s := s) (by rw [readOpLocC, _h]; exact _hl)
    omega

/-- What a frame completes: the blocks of a region of a kind or of a body,
a block, or an op. -/
inductive BDone where
  | blocks (kind : Option Name) (bs : List SBlock)
  | block (b : SBlock)
  | op (o : SOp)

/-- Hands what a frame completed to the frames `fs`, which read on by the
spec's readers. -/
def bFinish : BDone → List Token → List BFrame → Except ParseError (List SBlock × List Token)
  | .blocks _ bs, ts, [] => .ok (bs, ts)
  | .blocks kind bs, ts, .regions hd rs :: fs => do
    let ((), r₁) ← U (expect .rbrace "a block or } to close the region" ts)
    let (more, r₂) ← U (readRegions r₁)
    let (loc, r₃) ← U (readOpLoc r₂)
    bFinish (.op (hd.op ((⟨kind, bs⟩ :: rs).reverse ++ more) loc)) r₃ fs
  | .op o, ts, .ops l ps os :: fs => do
    let (more, r) ← U (readOps ts)
    bFinish (.block ⟨l, ps, (o :: os).reverse ++ more⟩) r fs
  | .block b, ts, .blocks kind bs :: fs => do
    let (more, r) ← U (readBlocks ts)
    bFinish (.blocks kind ((b :: bs).reverse ++ more)) r fs
  | _, ts, _ => .ok ([], ts)

/-- What `blocksLoop` computes from the frames `fs`, by the spec's
readers. -/
def bRun (ts : List Token) : List BFrame → Except ParseError (List SBlock × List Token)
  | [] => .ok ([], ts)
  | .blocks kind done :: fs => do
    let (bs, r) ← U (readBlocks ts)
    bFinish (.blocks kind (done.reverse ++ bs)) r fs
  | .ops l ps done :: fs => do
    let (os, r) ← U (readOps ts)
    bFinish (.block ⟨l, ps, done.reverse ++ os⟩) r fs
  | .regions hd done :: fs => do
    let (rs, r) ← U (readRegions ts)
    let (loc, r') ← U (readOpLoc r)
    bFinish (.op (hd.op (done.reverse ++ rs) loc)) r' fs

end FirRef
