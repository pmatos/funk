import Fir.Text.Decode

/-!
A file is bytes, and a fir text is UTF-8. Bytes that are not UTF-8 are a
parse error at the first byte of the first sequence that is not well formed
(Unicode, Table 3-7), as `funk` reports it.
-/

namespace FirRef

open Fir

/-- The bytes `b[i]` to `b[i + n - 1]` exist and are continuation bytes
(`0x80` to `0xbf`). -/
def continues (b : ByteArray) (i n : Nat) : Bool :=
  (List.range n).all fun k => match b[i + k]? with
    | some x => 0x80 ≤ x && x ≤ 0xbf
    | none => false

/-- The length of the well-formed UTF-8 sequence at `b[i]`, or 0 when the
sequence there is not well formed. -/
def seqLen (b : ByteArray) (i : Nat) : Nat :=
  match b[i]? with
  | none => 0
  | some x =>
    let second (lo hi : UInt8) : Bool := match b[i + 1]? with
      | some y => lo ≤ y && y ≤ hi
      | none => false
    if x < 0x80 then 1
    else if 0xc2 ≤ x && x ≤ 0xdf && continues b (i + 1) 1 then 2
    else if x = 0xe0 && second 0xa0 0xbf && continues b (i + 2) 1 then 3
    else if ((0xe1 ≤ x && x ≤ 0xec) || x = 0xee || x = 0xef) && continues b (i + 1) 2 then 3
    else if x = 0xed && second 0x80 0x9f && continues b (i + 2) 1 then 3
    else if x = 0xf0 && second 0x90 0xbf && continues b (i + 2) 2 then 4
    else if 0xf1 ≤ x && x ≤ 0xf3 && continues b (i + 1) 3 then 4
    else if x = 0xf4 && second 0x80 0x8f && continues b (i + 2) 2 then 4
    else 0

/-- The offset of the first byte from `i` on that does not start a
well-formed sequence, or the size of `b` when there is none. -/
def validUpTo (b : ByteArray) (i : Nat) : Nat :=
  if i < b.size then
    match h : seqLen b i with
    | 0 => i
    | n + 1 => validUpTo b (i + n + 1)
  else b.size
termination_by b.size - i

/-- Parses the bytes of a file with the dialect `d`. -/
def parseBytes {d : Dialect} [DialectText d] (b : ByteArray) : Except ParseError (Module d) :=
  match String.fromUTF8? b with
  | some text => parse text
  | none =>
    let n := validUpTo b 0
    let valid := (b.extract 0 n).toList
    let line := (valid.filter (· = 10)).length + 1
    let lineStart := match valid.reverse.findIdx? (· = 10) with
      | some k => n - k
      | none => 0
    .error ⟨⟨line, n - lineStart + 1⟩, "the text is not UTF-8"⟩

end FirRef
