import Fir.Core.RoundingText
import Fir.Core.Signature

/-!
# How the float arithmetic, the bit casts and the conversions are written

Each float op of arithmetic is written with its name, and each one that
rounds carries its rounding mode as one attribute, `round(r)`
(ADR-2026-11-09-1549, ADR-2026-11-11-1801). Every mode decodes, and M1's
validation accepts only `round(rne)`, round to nearest, ties to even. So

* `%s: f32 = fadd round(rne) %a, %b @1`, and `fsub`, `fmul` and `fdiv`
  likewise, take two values of one float type and give one of it;
* `%q: f64 = frem %a, %b @1` and `%q: f64 = fmod %a, %b @1` take two
  values and give one, and have no attribute: their result is exact;
* `%r: f64 = sqrt round(rne) %a @1` takes one value and gives one;
* `%n: f16 = fneg %a @1` and `%p: f16 = fabs %a @1` take one value and
  give one, and have no attribute: they do not round;
* `%f: bf16 = fma round(rne) %a, %b, %c @1` takes three values and gives
  `a * b + c`, rounded once;
* `%b: i32 = bitcast %f @1` takes a value of a float type and gives its
  bits as an integer of its width, and `%f: f32 = bitcast %b @1` the other
  way. It has no attribute: it does not round;
* `%f: f32 = sitofp round(rne) %i @1` takes a value of an integer type, of
  any width, and gives the integer it holds, read as signed, as a value of
  a float type, rounded; `uitofp` reads it as unsigned;
* `%d: f64 = fpext %f @1` takes a value of a float type and gives it as a
  value of a format that holds every value of it. It has no attribute: it
  does not round;
* `%f: f32 = fptrunc round(rne) %d @1` takes a value of a float type and
  gives it, rounded, as a value of a format that cannot hold every value
  of it;
* `%i: i32 = fptosi %f @1` takes a value of a float type and gives it,
  truncated toward zero, as a signed integer of any width; `fptoui` as an
  unsigned one. It has no attribute: it truncates, and does not round.

A float op, `fcmp` among them, may carry the fast-math flags before its
other attributes, each as a word, at most once, in the fixed order
`nnan`, `ninf`, `nsz`, `contract`, `reassoc`, as LLVM writes them:
`%s: f32 = fadd nnan nsz round(rne) %a, %b @1` and
`%c: i1 = fcmp ninf olt %a, %b @1`. `contract` and `reassoc` decode, so
that validation rejects them with its own reason: M2 decides them
(ADR-2026-11-09-1549). A flag out of order, or written twice, does not
decode, so each op has one spelling. The bit casts and the conversions
carry no flags.

The mode is written in the applied form of the grammar, as `float(e, m)`
is. Every op has one spelling: `fadd %a, %b` with no attribute does not
decode, and neither does `frem round(rne) %a, %b` or
`fneg round(rne) %a`, as a flag the op does not have does not.
`fadd round(rtz) %a, %b` decodes, with the mode `rtz`, and validation
rejects it: the modes other than `rne` are hooks in the format, as the
atomic orderings of a load are (the human's ruling of 2026-11-15 on
#229). The operands and the result of an op of arithmetic
have one float type, a bit cast's integer has its float's width, a
conversion from an integer takes an integer type and gives a float type,
a conversion between formats takes a float type and gives a float type,
a conversion to an integer takes a float type and gives an integer type,
and an op whose types are otherwise does not decode. Which pairs of
formats `fpext` and `fptrunc` take is a rule of validation, as the widths
of `zext` and `trunc` are, so both decode at any two formats.

This section gives the names of the ops, their attributes, and how an op
is read back, with the facts that the proof of the round trip uses.
-/

namespace Fir.Core

/-- The name of a float op of two operands. -/
def FBin.name : FBin → String
  | .fadd _ => "fadd" | .fsub _ => "fsub" | .fmul _ => "fmul" | .fdiv _ => "fdiv"
  | .frem => "frem" | .fmod => "fmod"

/-- The name of a float op of one operand. -/
def FUnary.name : FUnary → String
  | .fneg => "fneg" | .fabs => "fabs" | .sqrt _ => "sqrt"

/-- The flags as attributes: a word for each flag set, in the fixed order
`nnan`, `ninf`, `nsz`, `contract`, `reassoc`. -/
def FastMath.attrs (fl : FastMath) : List Attr :=
  (if fl.nnan then [.word "nnan"] else []) ++ (if fl.ninf then [.word "ninf"] else []) ++
    (if fl.nsz then [.word "nsz"] else []) ++ (if fl.contract then [.word "contract"] else []) ++
    (if fl.reassoc then [.word "reassoc"] else [])

/-- Takes the word `w` from the front of attributes: whether it was there,
and the attributes after it. -/
def takeWord (w : String) : List Attr → Bool × List Attr
  | .word v :: as => if v = w then (true, as) else (false, .word v :: as)
  | as => (false, as)

/-- Reads the flags from the front of attributes, each at most once and in
the fixed order: the flags, and the attributes after them. -/
def splitFlags (as : List Attr) : FastMath × List Attr :=
  let t1 := takeWord "nnan" as
  let t2 := takeWord "ninf" t1.2
  let t3 := takeWord "nsz" t2.2
  let t4 := takeWord "contract" t3.2
  let t5 := takeWord "reassoc" t4.2
  ({ nnan := t1.1, ninf := t2.1, nsz := t3.1, contract := t4.1, reassoc := t5.1 }, t5.2)

/-- Whether attributes do not start with a flag word, so that the flags
before them read back. -/
def flagFree : List Attr → Bool
  | .word v :: _ => !["nnan", "ninf", "nsz", "contract", "reassoc"].contains v
  | _ => true

/-- The attributes of a float op of two operands: its mode `round(r)`
for `fadd`, `fsub`, `fmul` and `fdiv`, and none for `frem` and `fmod`,
which do not round. -/
def FBin.attrs : FBin → List Attr
  | .fadd r | .fsub r | .fmul r | .fdiv r => [roundAttr r]
  | .frem | .fmod => []

/-- The attributes of a float op of one operand: its mode `round(r)` for
`sqrt`, and none for `fneg` and `fabs`, which do not round. -/
def FUnary.attrs : FUnary → List Attr
  | .sqrt r => [roundAttr r]
  | .fneg | .fabs => []

/-- The format of a float op of `k` operands: `float<e,m>` when the
operands are `k` values of it and the result is one. -/
def floatOpFormat (k : Nat) : List Ty → List Ty → Option (Nat × Nat)
  | ts, [.float e m] => if ts = List.replicate k (.float e m) then some (e, m) else none
  | _, _ => none

/-- Reads the attributes after the flags of the float op of two operands
named `n`: `round(r)`, with any mode `r`, for `fadd`, `fsub`, `fmul` and
`fdiv`, and none for `frem` and `fmod`. -/
def FBin.read : String → List Attr → Option FBin
  | "fadd", as => (decodeRound as).map .fadd
  | "fsub", as => (decodeRound as).map .fsub
  | "fmul", as => (decodeRound as).map .fmul
  | "fdiv", as => (decodeRound as).map .fdiv
  | "frem", as => if as.isEmpty then some .frem else none
  | "fmod", as => if as.isEmpty then some .fmod else none
  | _, _ => none

/-- Reads `fadd`, `fsub`, `fmul`, `fdiv`, `frem` or `fmod`, by its name
`n`: its flags, its other attributes, two operands and one result of one
float type. -/
def decodeFBin (n : String) (as : List Attr) (ts rs : List Ty) : Option Op :=
  let s := splitFlags as
  (FBin.read n s.2).bind fun o => (floatOpFormat 2 ts rs).map fun (e, m) => .fbin o s.1 e m

/-- Reads the attributes after the flags of the float op of one operand
named `n`: `round(r)`, with any mode `r`, for `sqrt`, and none for `fneg`
and `fabs`. -/
def FUnary.read : String → List Attr → Option FUnary
  | "sqrt", as => (decodeRound as).map .sqrt
  | "fneg", as => if as.isEmpty then some .fneg else none
  | "fabs", as => if as.isEmpty then some .fabs else none
  | _, _ => none

/-- Reads `fneg`, `fabs` or `sqrt`, by its name `n`: its flags, its other
attributes, one operand and one result of one float type. -/
def decodeFUnary (n : String) (as : List Attr) (ts rs : List Ty) : Option Op :=
  let s := splitFlags as
  (FUnary.read n s.2).bind fun o => (floatOpFormat 1 ts rs).map fun (e, m) => .funary o s.1 e m

/-- Reads `fma`: its flags, its mode `round(r)`, three operands and one
result of one float type. -/
def decodeFma (as : List Attr) (ts rs : List Ty) : Option Op :=
  let s := splitFlags as
  (decodeRound s.2).bind fun r => (floatOpFormat 3 ts rs).map fun (e, m) => .fma s.1 r e m

/-- Reads `bitcast`: no attributes, and one operand and one result, a
float type and an integer type of its width, in either order. -/
def decodeBitcast (as : List Attr) : List Ty → List Ty → Option Op
  | [.float e m], [.int w] => if as.isEmpty ∧ w = floatWidth e m then some (.toBits e m) else none
  | [.int w], [.float e m] => if as.isEmpty ∧ w = floatWidth e m then some (.ofBits e m) else none
  | _, _ => none

/-- Reads `sitofp`, with `signed`, or `uitofp`: its mode `round(r)`, one
operand of an integer type and one result of a float type. -/
def decodeIntToFloat (signed : Bool) (as : List Attr) : List Ty → List Ty → Option Op
  | [.int n], [.float e m] =>
    (decodeRound as).map fun r => if signed then .sitofp r n e m else .uitofp r n e m
  | _, _ => none

/-- Reads `fpext`: no attributes, one operand and one result of a float
type each, of any two formats. -/
def decodeFpext (as : List Attr) : List Ty → List Ty → Option Op
  | [.float e m], [.float e' m'] => if as.isEmpty then some (.fpext e m e' m') else none
  | _, _ => none

/-- Reads `fptrunc`: its mode `round(r)`, one operand and one result of a
float type each, of any two formats. -/
def decodeFptrunc (as : List Attr) : List Ty → List Ty → Option Op
  | [.float e m], [.float e' m'] => (decodeRound as).map (.fptrunc · e m e' m')
  | _, _ => none

/-- Reads `fptosi`, with `signed`, or `fptoui`: no attributes, one operand
of a float type and one result of an integer type. -/
def decodeFloatToInt (signed : Bool) (as : List Attr) : List Ty → List Ty → Option Op
  | [.float e m], [.int n] =>
    if as.isEmpty then some (if signed then .fptosi e m n else .fptoui e m n) else none
  | _, _ => none

/-! # Facts for the round trip -/

/-- Taking a word puts back what it took. -/
theorem takeWord_spec {w : String} {as r : List Attr} {b : Bool} (h : takeWord w as = (b, r)) :
    (if b then [Attr.word w] else []) ++ r = as := by
  unfold takeWord at h
  split at h
  · split at h <;> cases h <;> simp_all
  · cases h
    rfl

/-- The flags read from attributes, written back before the attributes
after them, are those attributes. -/
theorem splitFlags_spec (as : List Attr) :
    (splitFlags as).1.attrs ++ (splitFlags as).2 = as := by
  obtain ⟨b1, r1, h1⟩ : ∃ b r, takeWord "nnan" as = (b, r) := ⟨_, _, rfl⟩
  obtain ⟨b2, r2, h2⟩ : ∃ b r, takeWord "ninf" r1 = (b, r) := ⟨_, _, rfl⟩
  obtain ⟨b3, r3, h3⟩ : ∃ b r, takeWord "nsz" r2 = (b, r) := ⟨_, _, rfl⟩
  obtain ⟨b4, r4, h4⟩ : ∃ b r, takeWord "contract" r3 = (b, r) := ⟨_, _, rfl⟩
  obtain ⟨b5, r5, h5⟩ : ∃ b r, takeWord "reassoc" r4 = (b, r) := ⟨_, _, rfl⟩
  simp only [splitFlags, FastMath.attrs, h1, h2, h3, h4, h5, List.append_assoc]
  rw [takeWord_spec h5, takeWord_spec h4, takeWord_spec h3, takeWord_spec h2, takeWord_spec h1]

/-- A word that is not the flag word `w` is not taken as it. -/
theorem takeWord_free {w : String} {as : List Attr} (h : flagFree as = true)
    (hw : w ∈ ["nnan", "ninf", "nsz", "contract", "reassoc"]) : takeWord w as = (false, as) := by
  match as, h with
  | .word v :: _, h =>
    have hv : v ≠ w := fun e => by subst e; simp_all [flagFree]
    simp [takeWord, hv]
  | [], _ | .int _ :: _, _ | .str _ :: _, _ | .sym _ :: _, _ | .float _ :: _, _
  | .app .. :: _, _ => rfl

/-- The flags read back from their words, before attributes that do not
start with a flag word. -/
theorem splitFlags_attrs (fl : FastMath) {as : List Attr} (h : flagFree as = true) :
    splitFlags (fl.attrs ++ as) = (fl, as) := by
  have h1 := takeWord_free (w := "nnan") h (by simp)
  have h2 := takeWord_free (w := "ninf") h (by simp)
  have h3 := takeWord_free (w := "nsz") h (by simp)
  have h4 := takeWord_free (w := "contract") h (by simp)
  have h5 := takeWord_free (w := "reassoc") h (by simp)
  obtain ⟨a, b, c, d, e⟩ := fl
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;>
    simp_all [splitFlags, FastMath.attrs, takeWord]

/-- A float op of two operands read from a name and attributes has that
name and those attributes. -/
theorem FBin.read_eq {n : String} {as : List Attr} {o : FBin} (h : FBin.read n as = some o) :
    o.name = n ∧ o.attrs = as := by
  unfold FBin.read at h
  split at h <;> (try split at h) <;> simp_all [Option.map_eq_some_iff] <;>
    first
    | (obtain ⟨r, hr, rfl⟩ := h; exact ⟨rfl, (eq_of_decodeRound hr).symm⟩)
    | (subst_vars; exact ⟨rfl, rfl⟩)

/-- Each float op of two operands reads back from its name and attributes. -/
theorem FBin.read_name_attrs (o : FBin) : FBin.read o.name o.attrs = some o := by
  cases o <;> simp [FBin.read, FBin.name, FBin.attrs, decodeRound_roundAttr]

/-- A float op of one operand read from a name and attributes has that
name and those attributes. -/
theorem FUnary.read_eq {n : String} {as : List Attr} {o : FUnary} (h : FUnary.read n as = some o) :
    o.name = n ∧ o.attrs = as := by
  unfold FUnary.read at h
  split at h <;> (try split at h) <;> simp_all [Option.map_eq_some_iff] <;>
    first
    | (obtain ⟨r, hr, rfl⟩ := h; exact ⟨rfl, (eq_of_decodeRound hr).symm⟩)
    | (subst_vars; exact ⟨rfl, rfl⟩)

/-- Each float op of one operand reads back from its name and attributes. -/
theorem FUnary.read_name_attrs (o : FUnary) : FUnary.read o.name o.attrs = some o := by
  cases o <;> simp [FUnary.read, FUnary.name, FUnary.attrs, decodeRound_roundAttr]

/-- A float op's format is found only at its `k` operands and one result
of that format. -/
theorem floatOpFormat_eq {k : Nat} {ts rs : List Ty} {e m : Nat}
    (h : floatOpFormat k ts rs = some (e, m)) :
    ts = List.replicate k (.float e m) ∧ rs = [.float e m] := by
  unfold floatOpFormat at h
  split at h
  · split at h
    · cases h
      exact ⟨by assumption, rfl⟩
    · cases h
  · cases h

/-- A float op's format is found at its own operands and result. -/
theorem floatOpFormat_replicate (k e m : Nat) :
    floatOpFormat k (List.replicate k (.float e m)) [.float e m] = some (e, m) := by
  simp [floatOpFormat]

-- An op that rounds reads any mode, and one that does not reads none;
-- each op has its own number of operands.
#guard FBin.read "fadd" [roundAttr .rne] == some (.fadd .rne) &&
  FBin.read "fsub" [roundAttr .rtz] == some (.fsub .rtz) && FBin.read "fdiv" [] == none &&
  FBin.read "frem" [] == some .frem && FBin.read "frem" [roundAttr .rne] == none
#guard FUnary.read "sqrt" [roundAttr .rtp] == some (.sqrt .rtp) &&
  FUnary.read "fneg" [] == some .fneg && FUnary.read "fabs" [roundAttr .rtz] == none
#guard decodeFma [.word "nnan", roundAttr .rna] [.float 8 7, .float 8 7, .float 8 7] [.float 8 7] ==
  some (.fma { nnan := true } .rna 8 7) && decodeFma [] [.float 8 7, .float 8 7, .float 8 7] [.float 8 7] == none
#guard floatOpFormat 2 [.float 8 23, .float 8 23] [.float 8 23] == some (8, 23)
#guard floatOpFormat 2 [.float 8 23, .float 11 52] [.float 8 23] == none
#guard floatOpFormat 1 [.float 8 23, .float 8 23] [.float 8 23] == none
#guard floatOpFormat 1 [.int 32] [.int 32] == none
-- The flags read in their order, each at most once, and stop at the first
-- attribute that is not the next of them.
#guard (splitFlags [.word "nnan", .word "nsz", roundAttr .rne]).1 == { nnan := true, nsz := true } &&
  decodeRound (splitFlags [.word "nnan", .word "nsz", roundAttr .rne]).2 == some .rne
#guard (splitFlags [.word "nsz", .word "nnan", roundAttr .rne]).1 == { nsz := true } &&
  (splitFlags [.word "nsz", .word "nnan", roundAttr .rne]).2.length == 2
#guard (splitFlags [.word "ninf", .word "ninf"]).1 == { ninf := true } &&
  (splitFlags [.word "ninf", .word "ninf"]).2.length == 1
#guard (splitFlags [.word "contract", .word "reassoc", .word "olt"]).1 ==
  { contract := true, reassoc := true } &&
  (splitFlags [.word "contract", .word "reassoc", .word "olt"]).2.length == 1
-- A bit cast reads from the types which way it goes, and its widths must
-- match.
#guard decodeBitcast [] [.float 8 23] [.int 32] == some (.toBits 8 23)
#guard decodeBitcast [] [.int 16] [.float 8 7] == some (.ofBits 8 7)
#guard decodeBitcast [] [.float 8 23] [.int 64] == none &&
  decodeBitcast [] [.int 32] [.int 32] == none && decodeBitcast [] [.float 8 23] [.float 8 23] == none
#guard decodeBitcast [roundAttr .rne] [.float 8 23] [.int 32] == none

-- A conversion from an integer needs a mode, an integer operand and a
-- float result, of any width and format.
#guard decodeIntToFloat true [roundAttr .rne] [.int 32] [.float 8 23] == some (.sitofp .rne 32 8 23)
#guard decodeIntToFloat false [roundAttr .rne] [.int 1] [.float 15 112] ==
  some (.uitofp .rne 1 15 112)
#guard decodeIntToFloat true [] [.int 32] [.float 8 23] == none &&
  decodeIntToFloat true [.app "round" [.word "rtz"]] [.int 32] [.float 8 23] ==
    some (.sitofp .rtz 32 8 23)
#guard decodeIntToFloat false [roundAttr .rne] [.float 8 23] [.int 32] == none &&
  decodeIntToFloat false [roundAttr .rne] [.int 32] [.int 32] == none &&
  decodeIntToFloat true [roundAttr .rne] [.int 32, .int 32] [.float 8 23] == none

-- A conversion between formats takes a float to a float, of any two
-- formats; `fpext` has no attribute and `fptrunc` needs a mode.
#guard decodeFpext [] [.float 8 23] [.float 11 52] == some (.fpext 8 23 11 52)
#guard decodeFptrunc [roundAttr .rne] [.float 11 52] [.float 8 23] ==
  some (.fptrunc .rne 11 52 8 23)
#guard decodeFptrunc [roundAttr .rtn] [.float 11 52] [.float 8 23] ==
  some (.fptrunc .rtn 11 52 8 23)
#guard decodeFpext [] [.float 11 52] [.float 8 23] == some (.fpext 11 52 8 23)
#guard decodeFpext [roundAttr .rne] [.float 8 23] [.float 11 52] == none &&
  decodeFptrunc [] [.float 11 52] [.float 8 23] == none
#guard decodeFpext [] [.int 32] [.float 11 52] == none &&
  decodeFptrunc [roundAttr .rne] [.float 11 52] [.int 32] == none &&
  decodeFpext [] [.float 8 23, .float 8 23] [.float 11 52] == none

-- A conversion to an integer takes a float to an integer, of any format and
-- width, with no attribute: `round(rne)` and `round(rtz)` do not decode.
#guard decodeFloatToInt true [] [.float 8 23] [.int 32] == some (.fptosi 8 23 32)
#guard decodeFloatToInt false [] [.float 15 112] [.int 1] == some (.fptoui 15 112 1)
#guard decodeFloatToInt true [roundAttr .rne] [.float 8 23] [.int 32] == none &&
  decodeFloatToInt false [.app "round" [.word "rtz"]] [.float 8 23] [.int 32] == none
#guard decodeFloatToInt true [] [.int 32] [.float 8 23] == none &&
  decodeFloatToInt false [] [.float 8 23] [.float 8 23] == none &&
  decodeFloatToInt true [] [.float 8 23, .float 8 23] [.int 32] == none

end Fir.Core
