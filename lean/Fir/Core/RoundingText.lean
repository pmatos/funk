import Fir.Core.Rounding
import Fir.Syntax.Module

/-!
# The rounding mode in text

An op that rounds writes its mode as one attribute in the applied form of
the grammar, as `float(e, m)` is: `round(rne)`, `round(rna)`,
`round(rtp)`, `round(rtn)` or `round(rtz)`. Each of the five decodes, and
M1's validation accepts only `round(rne)` (ADR-2026-11-11-1801). Anything
else is not a mode and does not decode: a missing attribute, a word that
names no mode, as `round(RNE)` or `round(rnd)`, `round()`,
`round(rne, rne)`, the bare word `rne`, and two attributes.

This section gives the words of the modes, how a mode is written and read
back, and the facts that the proof of the round trip uses.
-/

namespace Fir.Core

/-- The word of a rounding mode. -/
def RoundingMode.word : RoundingMode → String
  | .rne => "rne"
  | .rna => "rna"
  | .rtp => "rtp"
  | .rtn => "rtn"
  | .rtz => "rtz"

/-- The rounding mode that a word names. -/
def decodeRoundingMode : String → Option RoundingMode
  | "rne" => some .rne
  | "rna" => some .rna
  | "rtp" => some .rtp
  | "rtn" => some .rtn
  | "rtz" => some .rtz
  | _ => none

/-- The attribute of an op that rounds with the mode `r`: `round(r)`. -/
def roundAttr (r : RoundingMode) : Attr := .app "round" [.word r.word]

/-- Reads the attributes of an op that rounds: exactly one, `round(r)`
with `r` the word of a mode. -/
def decodeRound : List Attr → Option RoundingMode
  | [.app "round" [.word w]] => decodeRoundingMode w
  | _ => none

/-- Each mode reads back from its word. -/
theorem decodeRoundingMode_word (r : RoundingMode) : decodeRoundingMode r.word = some r := by
  cases r <;> rfl

/-- The word of a mode is the only one that names it. -/
theorem word_of_decodeRoundingMode {w : String} {r : RoundingMode}
    (h : decodeRoundingMode w = some r) : r.word = w := by
  unfold decodeRoundingMode at h
  split at h <;> cases h <;> rfl

/-- Each mode reads back from how it is written. -/
theorem decodeRound_roundAttr (r : RoundingMode) : decodeRound [roundAttr r] = some r := by
  simp [roundAttr, decodeRound, decodeRoundingMode_word]

/-- Attributes that read as a mode are exactly how that mode is written. -/
theorem eq_of_decodeRound {as : List Attr} {r : RoundingMode} (h : decodeRound as = some r) :
    as = [roundAttr r] := by
  unfold decodeRound at h
  split at h
  · simp [roundAttr, word_of_decodeRoundingMode h]
  · cases h

/-- The attribute of a mode is written as tokens. -/
theorem roundAttr_writable (r : RoundingMode) : Attr.AllWritable [roundAttr r] := by
  have hr : isWord r.word := by cases r <;> decide
  simp [roundAttr, Attr.AllWritable, Attr.Writable, hr] <;> decide

-- Every mode decodes; nothing else does.
#guard [RoundingMode.rne, .rna, .rtp, .rtn, .rtz].all fun r => decodeRound [roundAttr r] == some r
#guard decodeRound [.app "round" [.word "rtz"]] == some .rtz
#guard decodeRound [] == none && decodeRound [.word "rne"] == none &&
  decodeRound [roundAttr .rne, roundAttr .rne] == none &&
  decodeRound [.app "round" [.word "RNE"]] == none && decodeRound [.app "round" []] == none &&
  decodeRound [.app "round" [.word "rne", .word "rne"]] == none

end Fir.Core
