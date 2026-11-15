import Fir.Core.Signature
import Fir.Validation.Layout
import Fir.Validation.Scope

/-!
The core dialect's part of validation: which core types are valid, which
symbols core ops refer to, the rules of `ret` and `call`, which read the
op's context, the width rules of `zext`, `sext` and `trunc`
(ADR-2026-10-29-2006), the format rules of `fpext` and `fptrunc` (the
human's ruling of 2026-11-12 on #354), the rule that no float op
carries a reserved word, `contract` or `reassoc` (ADR-2026-11-09-1549),
the rules of `alloca` (ADR-2026-11-14-0915), and the rules of `load`.
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

/-- An integer type: the types that M1's `alloca` allocates. -/
def Ty.IsInt : Ty → Prop
  | .int _ => True
  | _ => False

instance : DecidablePred Ty.IsInt := fun t => by
  cases t <;> unfold Ty.IsInt <;> infer_instance

/-- `call` refers to its callee's symbol; no other core op refers to one. -/
def Op.symbolRefs : Op → List String
  | .call f _ _ => [f]
  | _ => []

/-- The rounding mode of a float op of two operands: the mode of `fadd`,
`fsub`, `fmul` and `fdiv`, and none for `frem` and `fmod`, which do not
round. -/
def FBin.mode : FBin → Option RoundingMode
  | .fadd r | .fsub r | .fmul r | .fdiv r => some r
  | .frem | .fmod => none

/-- The rounding mode of a float op of one operand: the mode of `sqrt`,
and none for `fneg` and `fabs`, which do not round. -/
def FUnary.mode : FUnary → Option RoundingMode
  | .sqrt r => some r
  | .fneg | .fabs => none

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
* A float op that rounds, `fadd`, `fsub`, `fmul`, `fdiv`, `sqrt`, `fma`,
  `sitofp`, `uitofp` and `fptrunc`, rounds with the mode `rne`, round to
  nearest even, the one M1 accepts: the other modes are hooks in the
  format for a later milestone (ADR-2026-11-11-1801; the human's ruling
  of 2026-11-15 on #229).
* `alloca` allocates on the stack, the one kind M1 accepts: `global` and
  `heap` are hooks in the format, which a later milestone may accept
  (ADR-2026-11-09-1542). It allocates at least one value, aligned to a
  power of two of units (the human's ruling of 2026-11-11 on #231) no
  larger than `MemLayout.limit`, the data layout's rule for its own
  alignments (`MemLayout.ValidAlign`; the human's ruling of 2026-11-14 on
  #382), and its type is a valid integer type. Its count has no bound: an
  allocation larger than a machine holds is a resource error at run time,
  as a deep recursion is, and not a rule of validation. Its result names
  its memory, so the module's data layout checks that the module has that
  memory (ADR-2026-11-14-0915).
* `load` has the ordering `nonatomic`, the one M1 accepts: the other
  orderings are hooks in the format for a concurrency model
  (ADR-2026-11-09-1542). An alignment that it writes is a power of two no
  larger than `MemLayout.limit` (`MemLayout.ValidAlign`), as `alloca`'s
  is; one that it does not write is the natural alignment of its type in
  its memory. Its result is an integer type and its operand a pointer, and
  validation checks both types as it checks every type: the width is valid
  and the module has the memory.

Every other op has no rule beyond its signature.
-/
def Op.Valid (ctx : OpContext CoreDialect) : Op → Prop
  | .ret ts => ts = ctx.results
  | .call f ts rs => ctx.symbols f = some ⟨ts, rs⟩
  | .zext m n | .sext m n => m < n
  | .trunc m n => n < m
  | .fpext e m e' m' => e ≤ e' ∧ m ≤ m' ∧ ¬(e = e' ∧ m = m')
  | .fptrunc r e m e' m' => r = .rne ∧ ¬(e ≤ e' ∧ m ≤ m')
  | .sitofp r .. | .uitofp r .. => r = .rne
  | .fcmp _ fl .. => fl.Reserved = false
  | .fbin o fl .. => fl.Reserved = false ∧ ∀ r ∈ o.mode, r = .rne
  | .funary o fl .. => fl.Reserved = false ∧ ∀ r ∈ o.mode, r = .rne
  | .fma fl r .. => fl.Reserved = false ∧ r = .rne
  | .alloca k t c a _ => k = .stack ∧ 1 ≤ c ∧ (∀ x ∈ a, MemLayout.ValidAlign x) ∧
      t.IsInt ∧ t.Valid
  | .load o _ a _ => o = .nonatomic ∧ ∀ x ∈ a, MemLayout.ValidAlign x
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
