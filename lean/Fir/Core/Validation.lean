import Fir.Core.Signature
import Fir.Validation.Scope

/-!
The core dialect's part of validation: which core types are valid, which
symbols core ops refer to, the rules of `ret` and `call`, which read the
op's context, the width rules of `zext`, `sext` and `trunc`
(ADR-2026-10-29-2006), the format rules of `fpext` and `fptrunc` (the
human's ruling of 2026-11-12 on #354), and the rule that no float op
carries a reserved word, `contract` or `reassoc` (ADR-2026-11-09-1549).
The general rules of the previous sections already
check every op's operand and result types against its signature, so these
are all the rules of the core dialect. It has no rule over a whole function.
-/

namespace Fir.Core

/--
A core type is valid when it is `iN` with `1 ≤ N ≤ maxWidth`, or
`float<e,m>` with `e ≥ 2`, `m ≥ 1` and `1 + e + m ≤ maxWidth`. `i0` is not a
type. A float format needs at least 2 exponent bits and 1 mantissa bit, the
smallest that Lean's float model accepts, and is no wider than the widest
integer type (ADR-2026-11-09-1549). A pointer type `ptr<N>` is valid when
`N` is a memory number, at most `2^24 - 1`. Whether the module has memory
`N` is the rule of the module's data layout, which reads the memory that
the type names: every module has the default memory, so `ptr`, which is
`ptr<0>`, is always in it, and `ptr<N>` with `N ≥ 1` is when the layout
declares memory `N` (ADR-2026-11-12-1821).
-/
def Ty.Valid : Ty → Prop
  | .int w => 1 ≤ w ∧ w ≤ maxWidth
  | .float e m => 2 ≤ e ∧ 1 ≤ m ∧ floatWidth e m ≤ maxWidth
  | .ptr n => n ≤ maxMemory

/-- The memory that a core type points into: `N` for `ptr<N>`, and none for
an integer or a float. -/
def Ty.memory : Ty → Option Nat
  | .ptr n => some n
  | _ => none

/-- `call` refers to its callee's symbol; no other core op refers to one. -/
def Op.symbolRefs : Op → List String
  | .call f _ _ => [f]
  | _ => []

/--
The core rules of an op beyond its signature.

* `ret` returns values of the function's result types, any number of them.
* `call` passes and receives the types of its callee's signature, any
  number of each.
* `zext` and `sext` strictly widen, from `iM` to `iN` with `M < N`, and
  `trunc` strictly narrows, with `N < M`. A width change to the same width
  is not an op: the value itself is.
* `fpext` converts from `float<e,m>` to a format that holds every value of
  it, `float<e',m'>` with `e ≤ e'` and `m ≤ m'`, other than itself, so it
  never rounds. `fptrunc` converts to a format that cannot hold every
  value of the source, with `e' < e` or `m' < m`, and rounds. So every
  ordered pair of two formats takes exactly one of the two: `f32` to `f64`
  takes `fpext`, `f64` to `f32` takes `fptrunc`, and so do `bf16` to `f16`
  and `f16` to `bf16`, since `f16` has fewer exponent bits than `bf16` and
  more mantissa bits. A conversion to the same format is not an op.
* A float op carries neither `contract` nor `reassoc`. They are reserved
  words, permissions for passes that M2's optimizer decides, not meanings
  of an op (ADR-2026-11-09-1549).

Every other op has no rule beyond its signature.
-/
def Op.Valid (ctx : OpContext CoreDialect) : Op → Prop
  | .ret ts => ts = ctx.results
  | .call f ts rs => ctx.symbols f = some ⟨ts, rs⟩
  | .zext m n | .sext m n => m < n
  | .trunc m n => n < m
  | .fpext e m e' m' => e ≤ e' ∧ m ≤ m' ∧ ¬(e = e' ∧ m = m')
  | .fptrunc e m e' m' => ¬(e ≤ e' ∧ m ≤ m')
  | .fcmp _ fl .. | .fbin _ fl .. | .funary _ fl .. | .fma fl .. => fl.Reserved = false
  | _ => True

end Fir.Core

namespace Fir

instance : DialectValidation CoreDialect where
  validTy := Core.Ty.Valid
  symbolRefs := Core.Op.symbolRefs
  validOp := Core.Op.Valid
  validFunc _ _ _ := True
  tyMemory := Core.Ty.memory

end Fir
